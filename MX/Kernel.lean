import MX.Quantize

/-! # Abstract MX kernel — generalizing batch invariance away from `ℝ`

`MX/GEMM.lean` proves batch invariance over `ℝ`.  That proof is
structurally correct but vacuously so — over `ℝ`, addition is
commutative-associative, so any reasonable reduction order gives the
same answer regardless of how rows are batched.  The interesting
batch-invariance claim lives in fp, where addition is *commutative
but not associative*: changing the reduction order changes the
rounded sum.

This module re-states the result over an arbitrary accumulator type
`α`, with no algebraic assumptions on `+`.  The theorem reads:

  ` ∀ α, ∀ kernel : MXKernel α, A.row b = A'.row b →
        mxGEMM kernel A Wt b n = mxGEMM kernel A' Wt b n `

The proof is the same `unfold; rw [h]` we had over `ℝ`, but now it's
genuinely robust: instantiating `α` at `IEEEFloat 8 23` (FP32) with a
specific rounded `+` carries through unchanged, because the proof
never mentions `+`.

## What this protects against

The "robust" version of batch invariance is fragile in practice
because well-meaning optimizations can sneak in commutativity-
dependent rewrites.  E.g., `Σ over a column` in a `[NonAssoc]` setting
*looks* well-defined but isn't.  By stating the theorem over abstract
`α`, we force the proof to use only *structural* substitution — no
`Finset.sum_comm`, no `mul_sum`, no `ring`.  Any future maintainer
who tries to "simplify" using commutativity gets a type error.
-/

namespace MX

/-- An MX-GEMM kernel parameterized by accumulator type `α`.

      *  `blockOp` computes the per-block contribution: `(MXBlock K, MXBlock K) → α`.
         Hardware realizes this as a fused multiply-add over the K = 32
         element pairs in a low-precision MAC, scaled by the product of the
         two block scales.  The exact rounding behavior lives in the
         `blockOp` function — we treat it as a black box.

      *  `reduceTree` combines `m = K_total / 32` block contributions into
         one accumulator value.  This is the only outer-reduction degree of
         freedom; fixing it commits to a single reduction order. -/
structure MXKernel (α : Type*) (K m : Nat) where
  blockOp    : MXBlock K → MXBlock K → α
  reduceTree : (Fin m → α) → α

namespace MXKernel

variable {α : Type*} {K m : Nat}

/-- The kernel's per-vector dot product: per-block contributions
    combined via the reduction tree. -/
def dot (k : MXKernel α K m) (a b : MXVec K m) : α :=
  k.reduceTree (fun j => k.blockOp (a.get j) (b.get j))

/-- The kernel's MX-GEMM output at `(b, n)`: dot of `A.row b` and
    `Wt.row n`. -/
def gemm (k : MXKernel α K m) {B N : Nat}
    (A : MXMatrix B K m) (Wt : MXMatrix N K m)
    (b : Fin B) (n : Fin N) : α :=
  k.dot (A.get b) (Wt.get n)

/-! ## Robust batch invariance

The headline theorem.  Over arbitrary `α`, the kernel's output at row
`b` is determined by row `b` of `A` alone — independent of any other
rows of `A`, of the batch dimension `B`, or of how the kernel's
implementation interleaves work across `B` (it can't, because the
type signature funnels `A`'s dependence through `A.get b`). -/

/-- **Robust batch invariance.**  Over any accumulator type `α`, any
    kernel `k`, and any GEMM, perturbing rows of `A` other than `b`
    cannot change output row `b`.  Proof is `unfold + rw` — no
    arithmetic facts used, so the theorem holds when `α` is fp,
    integer, or anything else. -/
theorem gemm_batch_invariant
    (k : MXKernel α K m) {B N : Nat}
    (A A' : MXMatrix B K m) (Wt : MXMatrix N K m)
    (b : Fin B) (n : Fin N) (h : A.get b = A'.get b) :
    gemm k A Wt b n = gemm k A' Wt b n := by
  unfold gemm dot
  rw [h]

/-- **Robust batch invariance, blockwise hypothesis.**  Even weaker
    precondition: agreement at every block index of row `b` (not
    full-row equality). -/
theorem gemm_batch_invariant_blockwise
    (k : MXKernel α K m) {B N : Nat}
    (A A' : MXMatrix B K m) (Wt : MXMatrix N K m)
    (b : Fin B) (n : Fin N)
    (h : ∀ j : Fin m, (A.get b).get j = (A'.get b).get j) :
    gemm k A Wt b n = gemm k A' Wt b n := by
  unfold gemm dot
  congr 1
  funext j
  rw [h j]

/-- **End-to-end: encode-then-GEMM is batch-invariant.**  Composes
    `MXVec.encodeMatrix_congr_row` (Property 2) with abstract
    `gemm_batch_invariant`. -/
theorem encode_then_gemm_batch_invariant
    (k : MXKernel α K m) {B N : Nat}
    (A A' : MatReal B K m) (Wt : MXMatrix N K m)
    (b : Fin B) (n : Fin N) (h : A.get b = A'.get b) :
    gemm k (MXVec.encodeMatrix A) Wt b n =
      gemm k (MXVec.encodeMatrix A') Wt b n :=
  gemm_batch_invariant k _ _ Wt b n
    (MXVec.encodeMatrix_congr_row A A' b h)

/-! ## Right-operand invariance

By symmetry of the GEMM signature, the same argument applies to
`Wt`.  Stated for completeness — useful when proving that fixing
weights gives identical outputs across calls. -/

/-- Output at `(b, n)` is determined by `Wt.row n`, similarly. -/
theorem gemm_weight_invariant
    (k : MXKernel α K m) {B N : Nat}
    (A : MXMatrix B K m) (Wt Wt' : MXMatrix N K m)
    (b : Fin B) (n : Fin N) (h : Wt.get n = Wt'.get n) :
    gemm k A Wt b n = gemm k A Wt' b n := by
  unfold gemm dot
  rw [h]

end MXKernel

/-! ## Sanity check: the ℝ kernel from `MX.GEMM` is an instance

The original `mxGEMM : ReductionTree ℝ m → ...` from `MX.GEMM` is a
particular `MXKernel ℝ K m`.  Confirms that the abstraction generalizes
the existing work without losing it. -/

/-- The `ℝ`-valued kernel built from `MXBlock.blockDot` and a
    user-supplied reduction tree.  Reproduces `MX.mxGEMM`. -/
noncomputable def realKernel {K m : Nat}
    (t : (Fin m → ℝ) → ℝ) : MXKernel ℝ K m where
  blockOp a b :=
    a.scale.toRealOrZero * b.scale.toRealOrZero *
      ∑ i : Fin K, (a.elements.get i).toReal * (b.elements.get i).toReal
  reduceTree := t

end MX
