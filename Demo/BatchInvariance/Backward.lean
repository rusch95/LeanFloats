import Demo.BatchInvariance.Forward

/-! # Backward-pass batch invariance

The forward pass (`MX/Forward.lean`) shows that a layer's output at
row `b` depends only on input row `b`.  This module proves the dual
property for the backward pass: the *input* gradient at row `b`
depends only on the *output* gradient at row `b` (plus the layer's
weights and the forward state).

The backward pass through a layer `Y = act(W · X)` decomposes into
two steps:

  1. **Activation backward.**  `dZ[n] = act_grad(Z[n], dY[n])` where
     `Z = W · X` is the pre-activation.  Pointwise per output unit;
     trivially row-local.
  2. **GEMM transpose.**  `dX[i] = Σₙ W[n, i] · dZ[n]`.  The
     reduction dimension is `N` (number of output units), and the
     reduction order needs to be fixed for fp determinism — but it
     does *not* sum across batch rows, so each row's `dX` is
     independent of other rows.

Combining: input gradient at row `b` is a function of `(X.get b,
dY.get b, weights, kernels, actGrad)` — no other batch rows enter.

## Asymmetry with weight gradient

The *input* gradient is row-local.  The **weight gradient**
`dW[n, i] = Σ_b X[b, i] · dZ[b, n]` sums across batch.  So:

  *  Per-sample weight gradient `dW_per_sample[b, n, i] = X[b, i] ·
     dZ[b, n]` is row-local.
  *  Aggregate weight gradient `dW = Σ_b dW_per_sample[b, ·, ·]` is
     not — it explicitly sums over `B`.

This asymmetry is fundamental, not a quirk of our formalization.  We
state both pieces explicitly: per-sample contributions are
row-local; the across-batch sum has its own (B-dimensional)
reduction tree, and *that* tree's choice is what determines the fp
determinism of the weight gradient.

## What we model and what we don't

  *  We treat the input gradient as α-typed throughout (no
     re-quantization to MX during a single backward pass).  Real
     training stacks dequantize MX weights to FP32 on-demand inside
     the transpose-GEMM and produce FP32 gradients.

  *  The transpose-GEMM is abstracted as a `BwdKernel`: a function
     `(Fin N → α) → Fin (K · m) → α`.  We don't pin down its
     reduction-tree structure — we only need it to be a *function*
     of its single-row input, which is automatic.

  *  We don't model gradient quantization or stochastic rounding
     for QAT.  Those are downstream layers on top of this.
-/

namespace Demo.BatchInvariance
namespace Backward
open MX

/-! ## The backward kernel: transpose-GEMM -/

/-- A backward GEMM kernel for a single layer at a single batch row.
    Given an upstream gradient `dY : Fin N → α` (one row's worth),
    produces a downstream gradient `dX : Fin (K · m) → α`.

    The forward weights are baked in via closure when this structure
    is constructed.  The reduction order over `N` lives inside
    `inputGrad` — same as for the forward kernel, fixing this gives
    bitwise determinism in fp. -/
structure BwdKernel (α : Type*) (K m N : Nat) where
  inputGrad : (Fin N → α) → Fin (K * m) → α

/-! ## A single layer backward

Bundles the forward layer (for weights and forward kernel),
the activation gradient, and the transpose-GEMM kernel. -/

/-- A layer's backward operator.  Encapsulates everything needed to
    propagate gradients through one layer.

      *  `fwd`     — the forward layer (used to compute pre-activation `Z`).
      *  `actGrad` — `(z, dy) ↦ dz`: pointwise activation gradient.
      *  `bwd`    — transpose-GEMM kernel mapping `dZ ↦ dX`. -/
structure LayerBwd (α : Type*) (K m N : Nat) where
  fwd     : Forward.Layer α K m N
  actGrad : α → α → α
  bwd     : BwdKernel α K m N

namespace LayerBwd

variable {α : Type*} {K m N : Nat}

/-- The pre-activation values `Z = W · X` at a single input row. -/
def preAct (LB : LayerBwd α K m N) (x : MXVec K m) : Fin N → α :=
  fun n => LB.fwd.kernel.dot x (LB.fwd.weights.get n)

/-- Pointwise activation backward: `dZ = actGrad(Z, dY)`. -/
def activationBwd (LB : LayerBwd α K m N) (z dy : Fin N → α) : Fin N → α :=
  fun n => LB.actGrad (z n) (dy n)

/-- Full backward through a layer at a single row.  Given the input
    `x` and upstream gradient `dy`, produces the input gradient `dx`. -/
def apply (LB : LayerBwd α K m N) (x : MXVec K m) (dy : Fin N → α) :
    Fin (K * m) → α :=
  let z  := LB.preAct x
  let dz := LB.activationBwd z dy
  LB.bwd.inputGrad dz

/-- Backward applied to a whole batch.  At row `b`: take the b-th
    input row and the b-th gradient row, run `apply`. -/
def applyBatch {B : Nat}
    (LB : LayerBwd α K m N)
    (X : MXMatrix B K m) (dY : Fin B → Fin N → α) :
    Fin B → Fin (K * m) → α :=
  fun b => LB.apply (X.get b) (dY b)

/-! ## Row-independence of the input gradient -/

/-- **Single-layer backward row-independence.**  The input gradient
    at row `b` depends only on `X.get b` and `dY b` — not on any
    other batch rows of either input.

    Proof: `applyBatch` evaluates `apply (X.get b) (dY b)`, a pure
    function of those two row-slices.  Holds over any `α`, including
    fp accumulators. -/
theorem applyBatch_row_indep {B : Nat}
    (LB : LayerBwd α K m N)
    (X X' : MXMatrix B K m)
    (dY dY' : Fin B → Fin N → α)
    (b : Fin B)
    (hX  : X.get b = X'.get b)
    (hdY : dY b = dY' b)
    (i : Fin (K * m)) :
    LB.applyBatch X dY b i = LB.applyBatch X' dY' b i := by
  unfold applyBatch apply preAct activationBwd
  rw [hX, hdY]

/-- The applied row equals `apply` on the row's slices. -/
theorem applyBatch_eq_apply {B : Nat}
    (LB : LayerBwd α K m N)
    (X : MXMatrix B K m) (dY : Fin B → Fin N → α) (b : Fin B) :
    LB.applyBatch X dY b = LB.apply (X.get b) (dY b) := rfl

end LayerBwd

/-! ## Per-sample weight gradient is row-local

`dW_per_sample[b, n, i] = X[b, i] · dZ[b, n]` is computed on a
per-row basis; aggregating across batch produces the actual weight
gradient.  We expose the per-sample contribution as its own
function and prove it's row-local; the across-batch reduction is
factored out so its tree choice can be inspected separately. -/

namespace WeightGrad

/-- Per-sample weight gradient contribution at one batch row.

    `perSample LB x dy n i = X[i] · dZ[n]`, where `X` here means the
    decoded i-th element of the (block-quantized) input row at this
    batch row, and `dZ` is computed from `(z, dy)` via the
    activation gradient.

    This produces an `α`-typed contribution at every (n, i) pair —
    no across-batch reduction yet. -/
def perSample {α : Type*} {K m N : Nat}
    (LB : LayerBwd α K m N)
    (decodeX : MXVec K m → Fin (K * m) → α)
    (mulOp   : α → α → α)
    (x : MXVec K m) (dy : Fin N → α) :
    Fin N → Fin (K * m) → α :=
  let z  := LB.preAct x
  let dz := LB.activationBwd z dy
  fun n i => mulOp (decodeX x i) (dz n)

/-- Per-sample weight gradient over a whole batch. -/
def perSampleBatch {α : Type*} {K m N B : Nat}
    (LB : LayerBwd α K m N)
    (decodeX : MXVec K m → Fin (K * m) → α)
    (mulOp   : α → α → α)
    (X : MXMatrix B K m) (dY : Fin B → Fin N → α) :
    Fin B → Fin N → Fin (K * m) → α :=
  fun b => perSample LB decodeX mulOp (X.get b) (dY b)

/-- **Per-sample weight gradient is row-local.**  Each sample's
    contribution depends only on (X.get b, dY b).  The
    *across-batch sum* of these contributions is the actual weight
    gradient — and that sum is, by construction, not row-local. -/
theorem perSampleBatch_row_indep
    {α : Type*} {K m N B : Nat}
    (LB : LayerBwd α K m N)
    (decodeX : MXVec K m → Fin (K * m) → α)
    (mulOp   : α → α → α)
    (X X' : MXMatrix B K m)
    (dY dY' : Fin B → Fin N → α)
    (b : Fin B)
    (hX  : X.get b = X'.get b)
    (hdY : dY b = dY' b)
    (n : Fin N) (i : Fin (K * m)) :
    perSampleBatch LB decodeX mulOp X dY b n i =
      perSampleBatch LB decodeX mulOp X' dY' b n i := by
  unfold perSampleBatch perSample LayerBwd.preAct LayerBwd.activationBwd
  rw [hX, hdY]

/-- **Aggregate weight gradient.**  Sum across batch using a
    user-supplied reduction tree over `B`.  Bundled separately to
    make the across-batch reduction tree explicit — it's the
    *only* dependence on B in the whole backward pass. -/
def aggregate {α : Type*} {K m N B : Nat}
    (per : Fin B → Fin N → Fin (K * m) → α)
    (batchReduce : (Fin B → α) → α) :
    Fin N → Fin (K * m) → α :=
  fun n i => batchReduce (fun b => per b n i)

/-- The aggregate weight gradient at `(n, i)` depends on every batch
    row's contribution at that position.  This is the obverse of
    row-independence: there is no "agree at row b ⇒ agree" theorem
    here, because changing other rows changes the per-sample
    contributions and thus the sum.

    What we *can* say: the aggregate is *deterministic* given the
    reduction tree (`batchReduce`) and the per-sample contributions.
    This mirrors `MX.MXVec.dotBlockedTree_congr` for the GEMM's
    inner reduction — fix the tree, and the sum is a function. -/
theorem aggregate_deterministic
    {α : Type*} {K m N B : Nat}
    (per per' : Fin B → Fin N → Fin (K * m) → α)
    (batchReduce : (Fin B → α) → α)
    (h : ∀ b n i, per b n i = per' b n i) (n : Fin N) (i : Fin (K * m)) :
    aggregate per batchReduce n i = aggregate per' batchReduce n i := by
  unfold aggregate
  congr 1
  funext b
  rw [h b n i]

end WeightGrad

/-! ## General row-locality: closing the chain

`Forward.RowLocal` captures "this batch-shaped function depends only
on row `b` of its input."  We extend it to two-input functions
(`X` and `dY` both row-shaped) so the backward fits the same
abstraction. -/

/-- A two-input row-local function: at row `b`, the output depends
    only on `(X.get b, dY b)`. -/
def RowLocal2 {β : Type*} {K m N B : Nat} {γ : Type*}
    (f : MXMatrix B K m → (Fin B → Fin N → β) → Fin B → γ) : Prop :=
  ∀ X X' : MXMatrix B K m, ∀ dY dY' : Fin B → Fin N → β, ∀ b : Fin B,
    X.get b = X'.get b → dY b = dY' b →
    f X dY b = f X' dY' b

/-- A `LayerBwd.applyBatch` is two-input row-local. -/
theorem LayerBwd.applyBatch_rowLocal2 {α : Type*} {K m N B : Nat}
    (LB : LayerBwd α K m N) :
    @RowLocal2 α K m N B (Fin (K * m) → α)
      (fun X dY b => LB.applyBatch X dY b) := by
  intro X X' dY dY' b hX hdY
  funext i
  exact LB.applyBatch_row_indep X X' dY dY' b hX hdY i

end Backward
end Demo.BatchInvariance
