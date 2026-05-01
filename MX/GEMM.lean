import MX.Reduction

/-! # Batch invariance of MX-GEMM

The headline batch-invariance theorem.  Given a kernel whose outer
reduction tree depends only on the contraction dimension `m`, the
output at row `b` of the GEMM is determined by row `b` of the
left-hand side alone — perturbing or adding other rows cannot change
it.  This is what an LLM inference stack needs in order to guarantee
per-sequence reproducibility under batching.

## Setup

The kernel computes
  `Y[b, n] = dotBlockedTree t (A.row b) (Wᵀ.row n)`
where `A : MXMatrix B K m` and `Wt = Wᵀ : MXMatrix N K m`.  Storing
the right operand as `Wᵀ` rather than `W` matches the kernel's
access pattern (it iterates rows of A and rows of Wᵀ symmetrically).

## What Property 7 says

`mxGEMM_batch_invariant`: if `A.get b = A'.get b`, then
`mxGEMM t A Wt b n = mxGEMM t A' Wt b n`.  After the upstream work
in Properties 2, 4, and 5, this is a one-line corollary — the
*content* lives in the precondition on the kernel ("`t` depends only
on `m`") which is encoded by simply *taking* `t : ReductionTree ℝ m`
as a parameter.  A kernel whose reduction tree depended on `B` or on
the tile shape would have a different signature.

## What Property 7 does NOT say

  *  Nothing about correctness — `mxGEMM t` is parameterized by an
     arbitrary tree `t`, including silly ones.  The "tree computes
     the right answer" statement is `t.IsSumOver` (Property 5) and is
     orthogonal to batch invariance.
  *  Nothing about fp accumulator rounding — the entire chain is over
     `ℝ`.  Lifting to a rounded fp accumulator is a future module;
     the structure of the proof should carry over because the only
     property of `+` we use is "fixed-tree application is a function".

## What this combines with elsewhere

  *  `MXVec.encodeMatrix_congr_row` (Property 2 in `MX/Quantize.lean`)
     lifts row-equality through quantization.  Combined with
     `mxGEMM_batch_invariant`, we get end-to-end batch invariance from
     the real-valued input matrix all the way to the GEMM output:
     `encode_then_mxGEMM_batch_invariant` below.

  *  `MXVec.dotBlockedTree_tree_irrelevant_over_reals` (Property 5)
     gives, over `ℝ`, an extra layer of robustness: not only is the
     output deterministic for fixed `t`, but in fact any *valid* `t`
     (one that sums) produces the same answer.  Over fp this layer
     would dissolve.
-/

namespace MX

variable {B N K m : Nat}

/-- The MX-GEMM output at row `b`, column `n`: the block-factored dot
    product of `A`'s row `b` with `Wᵀ`'s row `n`, evaluated through the
    kernel's chosen outer reduction tree `t`.

    The reduction tree `t : ReductionTree ℝ m` depends *only* on the
    contraction dimension `m = K_total / 32`.  In particular it does
    not vary with `B`, `N`, or any tile shape — that's the structural
    constraint encoded in the function signature.  -/
noncomputable def mxGEMM
    (t : ReductionTree ℝ m) (A : MXMatrix B K m) (Wt : MXMatrix N K m)
    (b : Fin B) (n : Fin N) : ℝ :=
  MXVec.dotBlockedTree t (A.get b) (Wt.get n)

/-! ## Property 7 — batch invariance

The output at `(b, n)` is determined by `A.get b` and `Wt.get n` alone. -/

/-- **Property 7: batch invariance of MX-GEMM.**  If two left-hand-side
    matrices agree at row `b`, the GEMM output at row `b` is the same
    in both cases — regardless of any differences at other rows of `A`,
    of the batch dimension `B`, or of how the kernel tiles `B`/`N`.

    Direct corollary of the kernel's signature: because `t` depends only
    on `m` (and `mxGEMM` evaluates `t` against per-block products from
    `A.get b` and `Wt.get n`), the dependence on `A` is funneled
    entirely through `A.get b`. -/
theorem mxGEMM_batch_invariant
    (t : ReductionTree ℝ m) (A A' : MXMatrix B K m) (Wt : MXMatrix N K m)
    (b : Fin B) (n : Fin N) (h : A.get b = A'.get b) :
    mxGEMM t A Wt b n = mxGEMM t A' Wt b n := by
  unfold mxGEMM
  rw [h]

/-- **Batch invariance, blockwise form.**  Even weaker hypothesis: if
    `A` and `A'` agree at row `b` *block by block* (i.e., for every
    block index `j`), the output at `(b, n)` agrees.  Comes from
    `dotBlockedTree_congr` (Property 5), which only needs pointwise
    block-level agreement. -/
theorem mxGEMM_batch_invariant_blockwise
    (t : ReductionTree ℝ m) (A A' : MXMatrix B K m) (Wt : MXMatrix N K m)
    (b : Fin B) (n : Fin N)
    (h : ∀ j : Fin m, (A.get b).get j = (A'.get b).get j) :
    mxGEMM t A Wt b n = mxGEMM t A' Wt b n := by
  unfold mxGEMM
  exact MXVec.dotBlockedTree_congr t (A.get b) (A'.get b) (Wt.get n) (Wt.get n)
    h (fun _ => rfl)

/-- **End-to-end batch invariance: encode-then-GEMM.**  For real-valued
    input matrices `A`, `A'` that agree at row `b`, the encoded-and-
    multiplied output at row `b` agrees.  Composes Property 2
    (`encodeMatrix_congr_row`) with Property 7 (`mxGEMM_batch_invariant`).

    This is the form an inference engineer cites when arguing that
    "batching does not perturb per-sequence outputs": start from real-
    valued activations, prove that quantizing-then-multiplying preserves
    per-row outputs.  The chain is:

      *  Property 2: `(encodeMatrix A).get b = encodeRow (A.get b)`
         depends only on `A.get b`.
      *  Property 4: `dotBlocked` factors block scales out cleanly,
         shrinking the outer reduction to `m` terms.
      *  Property 5: with a fixed outer reduction tree `t`, the
         m-wide reduction is a pure function.
      *  Property 7 (this theorem): the GEMM output at row `b` is a
         function of (A.row b, Wt) only. -/
theorem encode_then_mxGEMM_batch_invariant
    (t : ReductionTree ℝ m) (A A' : MatReal B K m) (Wt : MXMatrix N K m)
    (b : Fin B) (n : Fin N) (h : A.get b = A'.get b) :
    mxGEMM t (MXVec.encodeMatrix A) Wt b n =
      mxGEMM t (MXVec.encodeMatrix A') Wt b n :=
  mxGEMM_batch_invariant t (MXVec.encodeMatrix A) (MXVec.encodeMatrix A') Wt b n
    (MXVec.encodeMatrix_congr_row A A' b h)

/-! ## Tree-irrelevance corollary (over ℝ)

Specialized to reals, the choice of reduction tree drops out for any
*valid* (sum-computing) tree.  Stated for completeness — the
operative form is `mxGEMM_batch_invariant`, which holds for any
fixed tree, valid or not.  Over fp this corollary fails. -/

/-- **Over ℝ, the GEMM output is tree-independent for any valid tree.**
    Two valid sum trees produce the same `mxGEMM` output.  This shows
    why batch invariance over reals is "easy": we don't even need to
    fix the tree, since any tree that sums gives the same answer.  In
    fp this fails and Property 7's fixed-`t` quantification matters. -/
theorem mxGEMM_tree_irrelevant_over_reals
    (t1 t2 : ReductionTree ℝ m)
    (h1 : t1.IsSumOver) (h2 : t2.IsSumOver)
    (A : MXMatrix B K m) (Wt : MXMatrix N K m) (b : Fin B) (n : Fin N) :
    mxGEMM t1 A Wt b n = mxGEMM t2 A Wt b n := by
  unfold mxGEMM
  exact MXVec.dotBlockedTree_tree_irrelevant_over_reals t1 t2 h1 h2 _ _

/-! ## Property 7 lifted to a generic accumulator

Real MXFP4 kernels accumulate block products in a rounded fp type
(FP32, BF16) rather than in `ℝ`.  Following `MX/Reduction.lean`'s
`dotBlockedTreeAcc`, we parameterize the GEMM by an accumulator
`Acc`, a per-block rounding function `round : ℝ → Acc`, and a
reduction tree `t : ReductionTree Acc m`.

Property 7 lifts unchanged: the proof of batch invariance only
appeals to "fixed tree is a function of its inputs," which is type-
generic.  Specializing `Acc := IEEEFloat 8 23` with nearest-even
rounding gives the bit-level batch-invariance theorem an inference
stack actually wants — the formal counterpart of the Thinking
Machines blog post's central claim that a kernel committing to a
fixed-by-`m` reduction tree achieves per-sequence reproducibility
under arbitrary batching. -/

/-- The MX-GEMM output evaluated through an arbitrary outer
    accumulator.  Each block product is rounded into `Acc` via
    `round` before entering the m-wide reduction `t`.

    `Acc := ℝ`, `round := id` recovers `mxGEMM`; see
    `mxGEMMAcc_id_eq_mxGEMM`. -/
noncomputable def mxGEMMAcc {Acc : Type*}
    (round : ℝ → Acc) (t : ReductionTree Acc m)
    (A : MXMatrix B K m) (Wt : MXMatrix N K m)
    (b : Fin B) (n : Fin N) : Acc :=
  MXVec.dotBlockedTreeAcc round t (A.get b) (Wt.get n)

/-- `Acc := ℝ`, `round := id` recovers `mxGEMM`. -/
theorem mxGEMMAcc_id_eq_mxGEMM
    (t : ReductionTree ℝ m) (A : MXMatrix B K m) (Wt : MXMatrix N K m)
    (b : Fin B) (n : Fin N) :
    mxGEMMAcc id t A Wt b n = mxGEMM t A Wt b n := rfl

/-- **Property 7 over an arbitrary accumulator: bit-level batch
    invariance.**  For any `Acc`, any `round : ℝ → Acc`, and any
    fixed reduction tree `t : ReductionTree Acc m`: if the LHS
    matrices agree at row `b`, the GEMM output at `(b, n)` agrees,
    independent of all other rows of `A` and of the batch dimension
    `B`.

    Specialized to `Acc := IEEEFloat 8 23` (FP32) with nearest-even
    rounding, this is bit-level batch invariance for an FP32-
    accumulator MXFP4 GEMM.  The blog's "fix the kernel's reduction
    shape and your inference stack becomes deterministic" thesis is
    exactly this theorem read constructively. -/
theorem mxGEMMAcc_batch_invariant {Acc : Type*}
    (round : ℝ → Acc) (t : ReductionTree Acc m)
    (A A' : MXMatrix B K m) (Wt : MXMatrix N K m)
    (b : Fin B) (n : Fin N) (h : A.get b = A'.get b) :
    mxGEMMAcc round t A Wt b n = mxGEMMAcc round t A' Wt b n := by
  unfold mxGEMMAcc
  rw [h]

/-- **Batch invariance over `Acc`, blockwise form.**  Weaker hypothesis:
    if `A` and `A'` agree at row `b` block by block, the output at
    `(b, n)` agrees.  Direct from `dotBlockedTreeAcc_congr`. -/
theorem mxGEMMAcc_batch_invariant_blockwise {Acc : Type*}
    (round : ℝ → Acc) (t : ReductionTree Acc m)
    (A A' : MXMatrix B K m) (Wt : MXMatrix N K m)
    (b : Fin B) (n : Fin N)
    (h : ∀ j : Fin m, (A.get b).get j = (A'.get b).get j) :
    mxGEMMAcc round t A Wt b n = mxGEMMAcc round t A' Wt b n := by
  unfold mxGEMMAcc
  exact MXVec.dotBlockedTreeAcc_congr round t (A.get b) (A'.get b)
    (Wt.get n) (Wt.get n) h (fun _ => rfl)

/-- **End-to-end batch invariance over `Acc`: encode-then-GEMM.**  For
    real-valued input matrices that agree at row `b`, the encoded-and-
    multiplied output at `(b, n)` agrees in `Acc`.  Composes Property 2
    (`encodeMatrix_congr_row`) with `mxGEMMAcc_batch_invariant`. -/
theorem encode_then_mxGEMMAcc_batch_invariant {Acc : Type*}
    (round : ℝ → Acc) (t : ReductionTree Acc m)
    (A A' : MatReal B K m) (Wt : MXMatrix N K m)
    (b : Fin B) (n : Fin N) (h : A.get b = A'.get b) :
    mxGEMMAcc round t (MXVec.encodeMatrix A) Wt b n =
      mxGEMMAcc round t (MXVec.encodeMatrix A') Wt b n :=
  mxGEMMAcc_batch_invariant round t (MXVec.encodeMatrix A)
    (MXVec.encodeMatrix A') Wt b n
    (MXVec.encodeMatrix_congr_row A A' b h)

end MX
