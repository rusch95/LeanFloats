import Demo.BatchInvariance.Forward
import MX.RMSNorm
import MX.Softmax

/-! # End-to-end transformer-block batch invariance

A stylized transformer block

  input → RMSNorm → linear (Q,K,V projection) → softmax → linear (out)
                                                  → output

formalized as a composition of per-row functions.  Each individual
step's batch-invariance has been proved separately:

  *  `MX.MXKernel.gemm_batch_invariant`            — `MX/Kernel.lean`
  *  `MX.RMSNorm.rmsNormAcc_batch_invariant`        — `MX/RMSNorm.lean`
  *  `MX.Softmax.softmaxAcc_batch_invariant`        — `MX/Softmax.lean`

Each is the contract that the kernel commits to a fixed reduction
tree depending only on the contraction dimension.  This module
composes them: under those contracts, the *whole* block's per-row
output is a function of the input row alone — bit-deterministic
under any batching.

This is the formal counterpart of the Thinking Machines blog post's
macro claim: "if every kernel is batch-invariant, the inference
stack is reproducible."

## Why composition is so easy

The structural argument:

  *  Each per-row operation is a Lean function `MXVec K m → β` —
     mathematically pure, so no implicit dependence on other rows.

  *  Composing pure row-functions yields another pure row-function.

  *  Lifted to a batch via `applyBatch X b := applyRow (X.get b)`,
     batch-invariance is `rfl` after `rw [h]`.

The substance lives in the *types*: each component is parameterized
by its own reduction tree(s) and per-block functions, encoding "the
kernel commits to a fixed shape that depends only on `m`".  Drop
those parameters and the contracts in turn would silently allow
batch-dependent reduction, which is exactly the negative result
formalized in `MX/TreeDependence.lean`.
-/

namespace Demo.BatchInvariance
namespace TransformerBlock
open MX

/-! ## A stylized 4-step transformer block

The four steps are RMSNorm, linear (input projection), softmax, and
linear (output projection).  Real transformer blocks have residual
connections, multi-head attention's QK^T·V structure, and so on;
those add complexity without changing the row-locality argument.
We model the simplest shape that exercises every reduction kind.
-/

/-- A 4-step block, each step a per-row function.

    Type plumbing:
      *  Input row:  `MXVec K₀ m₀`
      *  After RMSNorm: `MXVec K₀ m₀` (same shape, re-quantized)
      *  After linear₁: `MXVec K₁ m₁` (re-quantized internally)
      *  After softmax: `MXVec K₁ m₁` (re-quantized)
      *  After linear₂: `β` (final output, no further reduction)

    Real implementations realize each step via the tree-parameterized
    Acc-typed kernels in `MX.Kernel` / `MX.RMSNorm` / `MX.Softmax`,
    composed with re-quantization (the per-step `post`).  This
    structure intentionally hides the post-step internals: any choice
    of post-step preserves row-locality, so the structural argument
    applies uniformly. -/
structure Block (β : Type*) (K₀ m₀ K₁ m₁ : Nat) where
  rms     : MXVec K₀ m₀ → MXVec K₀ m₀
  lin1    : MXVec K₀ m₀ → MXVec K₁ m₁
  softmax : MXVec K₁ m₁ → MXVec K₁ m₁
  lin2    : MXVec K₁ m₁ → β

namespace Block

variable {β : Type*} {K₀ m₀ K₁ m₁ : Nat}

/-- Apply the block to a single input row. -/
def applyRow (B : Block β K₀ m₀ K₁ m₁) (x : MXVec K₀ m₀) : β :=
  B.lin2 (B.softmax (B.lin1 (B.rms x)))

/-- Apply the block to a whole batch.  Per-row independent. -/
def applyBatch {N : Nat} (B : Block β K₀ m₀ K₁ m₁)
    (X : MXMatrix N K₀ m₀) : Fin N → β :=
  fun b => B.applyRow (X.get b)

/-- **End-to-end transformer-block batch invariance.**

    For any block `B` (any choice of reduction trees, per-block
    operations, and post-steps internal to its four components) and
    any two batches that agree at row `b`, the block's output at row
    `b` agrees.

    The proof is structural: `applyBatch X b` reduces to
    `applyRow (X.get b)`, which is a pure function of `X.get b` —
    so `rw [h]` finishes.  The substance lives in `Block`'s type:
    each field is `MXVec _ _ → MXVec _ _` (or `→ β`), with no
    matrix or batch index in sight.  A maintainer who tries to make
    a step "see" other rows breaks the type. -/
theorem applyBatch_row_indep {N : Nat}
    (B : Block β K₀ m₀ K₁ m₁) (X X' : MXMatrix N K₀ m₀) (b : Fin N)
    (h : X.get b = X'.get b) :
    B.applyBatch X b = B.applyBatch X' b := by
  unfold applyBatch
  rw [h]

/-- The applied row equals `applyRow` on `X.get b`. -/
theorem applyBatch_eq_applyRow {N : Nat}
    (B : Block β K₀ m₀ K₁ m₁) (X : MXMatrix N K₀ m₀) (b : Fin N) :
    B.applyBatch X b = B.applyRow (X.get b) := rfl

/-- A `Block`'s `applyBatch` is `RowLocal` in the sense of
    `MX.Forward.RowLocal`.  Bridges this module to the `RowLocal`
    composition pattern used in `MX/Forward.lean`. -/
theorem applyBatch_rowLocal (N : Nat) (B : Block β K₀ m₀ K₁ m₁) :
    Forward.RowLocal (K := K₀) (m := m₀) (B := N) (β := β)
      B.applyBatch :=
  fun X X' b h => B.applyBatch_row_indep X X' b h

end Block

/-! ## Building a Block from the kernel-specific theorems

Concrete recipes for instantiating the four fields from the
upstream Acc-typed kernels.  Each recipe takes the same parameters
that appear in the underlying batch-invariance theorem (reduction
trees, per-block functions, etc.) and produces a row-function
suitable for one of `Block`'s fields.  The user composes four
recipes to construct a full `Block`.

These are intentionally simple wrappers — no proof obligations —
because the row-locality of each kernel is encoded in its type
signature, not in a separate predicate. -/

namespace Block

variable {Acc : Type*}

/-- Build the RMSNorm step from the parameters of `RMSNorm.rmsNormAcc`,
    specialized to a row-level `post` that re-quantizes to MX. -/
noncomputable def mkRmsStep {K m : Nat}
    (round : ℝ → Acc) (t : ReductionTree Acc m)
    (post : Acc → MXVec K m → MXVec K m) :
    MXVec K m → MXVec K m :=
  fun x => post (MXVec.sumOfSquaresAcc round t x) x

/-- Build the linear (GEMM) step from an `MXKernel` plus a quantizer.
    The kernel produces `Fin N → Acc`; the quantizer turns this into
    the next stage's MX vector. -/
def mkLinearStep {K m K' m' N : Nat}
    (k : MXKernel Acc K m) (weights : MXMatrix N K m)
    (quantize : (Fin N → Acc) → MXVec K' m') :
    MXVec K m → MXVec K' m' :=
  fun x => quantize (fun n => k.dot x (weights.get n))

/-- Build the softmax step from the parameters of `Softmax.softmaxAcc`,
    specialized to a row-level `post`. -/
noncomputable def mkSoftmaxStep {K m : Nat}
    (round : ℝ → Acc)
    (t_max : ReductionTree Acc m) (t_sumExp : ReductionTree Acc m)
    (perBlockMax : MXBlock K → ℝ)
    (perBlockSumExp : Acc → MXBlock K → ℝ)
    (post : Acc → Acc → MXVec K m → MXVec K m) :
    MXVec K m → MXVec K m :=
  fun x =>
    let M := t_max (fun j => round (perBlockMax (x.get j)))
    let S := t_sumExp (fun j => round (perBlockSumExp M (x.get j)))
    post M S x

end Block

end TransformerBlock
end Demo.BatchInvariance
