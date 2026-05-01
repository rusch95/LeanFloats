import Demo.BatchInvariance.Forward
import Demo.BatchInvariance.Backward
import Demo.BatchInvariance.TransformerBlock

/-! # Backend abstraction for batch-invariance demo

A `Backend α` is the kernel-level interface the toy LLM is written
against.  It provides — for each kernel-shaped operation — a
**batched** implementation that takes a whole tensor.  The
*reference* per-row form is a plain Lean function (e.g.
`Forward.Layer.apply`); the backend's job is to deliver the batched
output, possibly with implementation-specific tricks.

A `BatchInvariant α` instance witnesses that, on every operation,
the batched implementation agrees pointwise with applying the
reference per-row function to each row in isolation:

  `Backend.layerApplyBatch L X b n = L.apply (X.get b) n`

For the canonical `MXBackend` (`Demo/BatchInvariance/Backend/MX.lean`)
the batched form is *defined* as `applyBatch ∘ get`, so each axiom
discharges by `rfl`.

The point of the abstraction is the *future* hostile backends —
those that model real-silicon trickiness:

  *  `SplitKBackend k` — cuBLAS-style split-K reduction with split
     factor `k(m, K, N)` that may depend on the batch dim.  Provides
     `BatchInvariant` only when `k` is batch-dim-independent.

  *  `TensorCoreBackend` — fp16×fp16→fp32 accumulation with a
     tensor-core-shaped reduction tree.  May satisfy
     `BatchInvariant` only at fixed tile sizes.

  *  `AtomicAddBackend` — concurrent atomic-add reduction whose
     order is launch-grid-dependent.  Witnesses *failure* of
     `BatchInvariant` with a concrete counterexample.

  *  `FMABackend` — fuses `a*b + c` into one rounded operation.
     Orthogonal to BI but breaks bitwise equivalence to `MXBackend`.

The headline theorem `toyLLM_batch_invariant` is stated parametric
in `[Backend α] [BatchInvariant α]`; instantiating it at a hostile
backend that fails `BatchInvariant` exposes precisely which axiom
breaks.

## What's in / what's not

The `Backend` axiomatizes the *layer-level* primitives —
`layerApplyBatch` (forward), `layerBwdApplyBatch` (input gradient),
and `weightGradPerSampleBatch`.  Higher-level building blocks
(transformer block, multi-head attention, multi-layer stack) are
*derived* from these via composition — so block-level batch
invariance is a theorem, not an axiom.  This keeps the
`BatchInvariant` interface minimal and surfaces clearly which
primitive a hostile backend would need to break. -/

namespace Demo.BatchInvariance
open MX

/-- The kernel-level interface the toy LLM composes.  Each field is a
    *batched* operation; the corresponding per-row reference is a
    plain Lean function (e.g. `L.apply`). -/
class Backend (α : Type) where
  /-- Forward through one fully-connected layer (GEMM + activation),
      on a batch.  Friendly form: `L.applyBatch X b n` (defined as
      `L.apply (X.get b) n`); hostile forms are free to differ. -/
  layerApplyBatch {K m N B : Nat} :
    Forward.Layer α K m N → MXMatrix B K m → Fin B → Fin N → α
  /-- Backward through one layer: input gradient on a batch. -/
  layerBwdApplyBatch {K m N B : Nat} :
    Backward.LayerBwd α K m N →
    MXMatrix B K m → (Fin B → Fin N → α) →
    Fin B → Fin (K * m) → α
  /-- Per-sample weight-gradient contribution on a batch.  The
      across-batch sum is *not* part of the backend (its tree choice
      is its own concern; see `Backward.WeightGrad.aggregate`). -/
  weightGradPerSampleBatch {K m N B : Nat} :
    Backward.LayerBwd α K m N →
    (MXVec K m → Fin (K * m) → α) →     -- decodeX
    (α → α → α) →                       -- mulOp
    MXMatrix B K m → (Fin B → Fin N → α) →
    Fin B → Fin N → Fin (K * m) → α

/-- A backend is **batch-invariant** if every batched primitive
    agrees pointwise with applying the canonical per-row reference
    to each row in isolation.  Equivalently: there is no cross-batch
    coupling in the implementation.

    Each axiom names the per-row reference explicitly, so failure
    diagnostics on a hostile backend point at the specific
    primitive whose implementation introduces coupling. -/
class BatchInvariant (α : Type) [Backend α] : Prop where
  /-- Layer forward: batched output at `(b, n)` equals row apply
      at `n` of the `b`-th input row. -/
  layer_batch_eq_apply :
    ∀ {K m N B : Nat} (L : Forward.Layer α K m N)
      (X : MXMatrix B K m) (b : Fin B) (n : Fin N),
      Backend.layerApplyBatch L X b n = L.apply (X.get b) n
  /-- Layer backward (input gradient): batched output at `(b, i)`
      equals row apply at `i` of `(X.get b, dY b)`. -/
  layerBwd_batch_eq_apply :
    ∀ {K m N B : Nat} (LB : Backward.LayerBwd α K m N)
      (X : MXMatrix B K m) (dY : Fin B → Fin N → α)
      (b : Fin B) (i : Fin (K * m)),
      Backend.layerBwdApplyBatch LB X dY b i = LB.apply (X.get b) (dY b) i
  /-- Per-sample weight gradient: batched output at `(b, n, i)`
      equals the row-level per-sample contribution. -/
  weightGrad_batch_eq_apply :
    ∀ {K m N B : Nat} (LB : Backward.LayerBwd α K m N)
      (decodeX : MXVec K m → Fin (K * m) → α) (mulOp : α → α → α)
      (X : MXMatrix B K m) (dY : Fin B → Fin N → α)
      (b : Fin B) (n : Fin N) (i : Fin (K * m)),
      Backend.weightGradPerSampleBatch LB decodeX mulOp X dY b n i =
        Backward.WeightGrad.perSample LB decodeX mulOp (X.get b) (dY b) n i

end Demo.BatchInvariance
