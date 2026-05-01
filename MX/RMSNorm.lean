import MX.GEMM_FP32

/-! # RMSNorm batch invariance

RMSNorm of a single row `x` of length `K · m` is

  rms(x) = √(Σ_i x_i² / (K · m)) + ε
  y_i    = γ_i · x_i / rms(x)

The only reduction is the sum-of-squares.  All other operations are
elementwise (square, scale by `γ`, divide by `rms`), so they don't
introduce any reduction-shape dependency.  The blog-post claim
specializes: if the kernel commits a reduction tree depending only
on the contraction dimension `m` (= feature_dim / 32), per-row
output is bit-deterministic across batchings.

## Reuse from GEMM

`Σ_i x_i² = dotBlocked x x` exactly — sum-of-squares is the
self-dot product.  So `MX.MXVec.dotBlockedTreeAcc round t x x` is
already the "sum-of-squares with explicit reduction tree."  The
batch-invariance proof is then a one-line corollary of
`dotBlockedTreeAcc_congr` (Property 5 over `Acc`).

The post-reduction step (sqrt, divide, multiply by `γ`) is
modeled abstractly as a function `Acc → MXVec K m → β`: anything
the kernel does with the row's sum-of-squares to produce its
final output.  Batch-invariance of the *whole* RMSNorm reduces
to batch-invariance of the sum-of-squares — which is what this
module's headline theorem says.
-/

namespace MX

namespace MXVec

variable {K m : Nat}

/-- Sum-of-squares of an MX vector, evaluated through an outer
    accumulator.  Definitionally equal to `dotBlockedTreeAcc round t x x`
    — sum-of-squares is the self-dot product, with the per-block
    scales squared by `dotBlocked`'s factorization (Property 4 in
    `MX/Dot.lean`). -/
noncomputable def sumOfSquaresAcc {Acc : Type*}
    (round : ℝ → Acc) (t : ReductionTree Acc m) (x : MXVec K m) : Acc :=
  dotBlockedTreeAcc round t x x

/-- The sum-of-squares is the self-dot product. -/
theorem sumOfSquaresAcc_eq_dotBlockedTreeAcc_self {Acc : Type*}
    (round : ℝ → Acc) (t : ReductionTree Acc m) (x : MXVec K m) :
    sumOfSquaresAcc round t x = dotBlockedTreeAcc round t x x := rfl

/-- **Sum-of-squares is row-local.**  For any fixed reduction tree,
    two MX vectors agreeing block-by-block produce the same
    sum-of-squares.  Direct corollary of `dotBlockedTreeAcc_congr`. -/
theorem sumOfSquaresAcc_congr {Acc : Type*}
    (round : ℝ → Acc) (t : ReductionTree Acc m) (x x' : MXVec K m)
    (h : ∀ j : Fin m, x.get j = x'.get j) :
    sumOfSquaresAcc round t x = sumOfSquaresAcc round t x' := by
  unfold sumOfSquaresAcc
  exact dotBlockedTreeAcc_congr round t x x' x x' h h

end MXVec

/-! ## RMSNorm at the batch level

The full RMSNorm of a row is `post (sumOfSquares row) row`, where
`post : Acc → MXVec K m → β` packages all the elementwise work
(sqrt, divide, multiply by gain).  We don't pin down `post` — its
batch-invariance properties are inherited automatically by virtue
of being a function of the row alone.

Lifted to a batch `X : MXMatrix B K m`, the per-row RMSNorm output
at row `b` is

  rmsNormAcc round t post X b = post (sumOfSquaresAcc round t (X.get b)) (X.get b)

and depends only on `X.get b`. -/

namespace RMSNorm

variable {Acc β : Type*} {B K m : Nat}

/-- RMSNorm at the batch level, abstracting the post-reduction step.
    Parameters:
      *  `round` — `ℝ → Acc` rounding (one per block)
      *  `t`     — outer reduction tree on `Acc` (depends only on `m`)
      *  `post`  — `(rms : Acc) → (row : MXVec K m) → β`, packaging
                    sqrt, divide, multiply-by-gain, etc.

    The kernel realizes the standard formula by instantiating `post`
    with `fun ss row => fun i => γ i · decoded(row, i) / sqrt(ss / n + ε)`. -/
noncomputable def rmsNormAcc
    (round : ℝ → Acc) (t : ReductionTree Acc m)
    (post : Acc → MXVec K m → β)
    (X : MXMatrix B K m) (b : Fin B) : β :=
  post (MXVec.sumOfSquaresAcc round t (X.get b)) (X.get b)

/-- **RMSNorm row-locality.**  For any fixed reduction tree and any
    post-reduction step, the RMSNorm output at row `b` depends only
    on `X.get b` — not on any other row of the batch, and not on the
    batch dimension `B`.

    Directly inherits from `sumOfSquaresAcc_congr` for the reduction
    step and is `rfl` for the post step (since `post` is applied to
    `(sumOfSquares (X.get b), X.get b)`, both of which are functions
    of `X.get b` alone). -/
theorem rmsNormAcc_batch_invariant
    (round : ℝ → Acc) (t : ReductionTree Acc m)
    (post : Acc → MXVec K m → β)
    (X X' : MXMatrix B K m) (b : Fin B) (h : X.get b = X'.get b) :
    rmsNormAcc round t post X b = rmsNormAcc round t post X' b := by
  unfold rmsNormAcc
  rw [h]

/-- Blockwise form: per-block agreement at row `b` suffices. -/
theorem rmsNormAcc_batch_invariant_blockwise
    (round : ℝ → Acc) (t : ReductionTree Acc m)
    (post : Acc → MXVec K m → β)
    (X X' : MXMatrix B K m) (b : Fin B)
    (h : ∀ j : Fin m, (X.get b).get j = (X'.get b).get j) :
    rmsNormAcc round t post X b = rmsNormAcc round t post X' b := by
  -- We need to derive `X.get b = X'.get b` from blockwise agreement.
  have hxx' : X.get b = X'.get b := by
    apply List.Vector.ext
    intro j
    exact h j
  exact rmsNormAcc_batch_invariant round t post X X' b hxx'

end RMSNorm

/-! ## FP32 specialization

`Acc := IEEEFloat 8 23`, `round := roundFP32`.  Bit-level batch
invariance for an FP32-accumulator MXFP4 RMSNorm with any fixed
outer reduction tree. -/

namespace RMSNorm

variable {β : Type*} {B K m : Nat}

/-- RMSNorm with an FP32 outer accumulator. -/
noncomputable def rmsNormFP32
    (t : ReductionTree (IEEEFloat 8 23) m)
    (post : IEEEFloat 8 23 → MXVec K m → β)
    (X : MXMatrix B K m) (b : Fin B) : β :=
  rmsNormAcc roundFP32 t post X b

/-- **Bit-level batch invariance for FP32-accumulator MXFP4 RMSNorm.**
    Specialization of `rmsNormAcc_batch_invariant` to FP32.  The
    Thinking Machines blog post's RMSNorm case study, formal. -/
theorem rmsNormFP32_batch_invariant
    (t : ReductionTree (IEEEFloat 8 23) m)
    (post : IEEEFloat 8 23 → MXVec K m → β)
    (X X' : MXMatrix B K m) (b : Fin B) (h : X.get b = X'.get b) :
    rmsNormFP32 t post X b = rmsNormFP32 t post X' b :=
  rmsNormAcc_batch_invariant roundFP32 t post X X' b h

end RMSNorm

end MX
