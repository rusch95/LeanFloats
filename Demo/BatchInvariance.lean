import Demo.BatchInvariance.Forward
import Demo.BatchInvariance.Backward
import Demo.BatchInvariance.TransformerBlock
import Demo.BatchInvariance.Backend
import Demo.BatchInvariance.Backend.MX
import Demo.BatchInvariance.Model

/-! # Demo: Batch invariance of a toy LLM

This demo proves that, for a stylized transformer-style LLM
implemented over the OCP MXFP4 spec, the per-batch-position output
on both the forward and backward passes is *bitwise identical* to
running that position alone in a singleton batch.  Other examples
in the batch cannot influence what example `i` sees — at the FP-bit
level, on either pass.

## The headline theorem

`toyLLM_batch_invariant`: for any backend `B` satisfying the
`BatchInvariant` interface, any architecture size `(L, H)`, any
parameters `θ`, any batch of inputs and targets, any batch position
`i`, and any permutation `σ` of the batch:

  1. Forward at row `i` equals the singleton forward.
  2. Input gradient at row `i` equals the singleton input gradient.
  3. Per-example parameter-gradient contribution at row `i` equals
     the singleton parameter gradient.
  4. Permuting the batch permutes the forward output likewise.
  5. Permuting the batch permutes the gradients likewise.

Stated parametrically over a `Backend` typeclass.  The concrete
`MXBackend` instance discharges the proof for the kernels currently
defined in `MX/`.  Future hostile backends modelling NVIDIA-style
split-K, tensor-core mixed-precision, atomic-add nondeterminism, or
FMA fusion can be added — they are expected to *fail* the
`BatchInvariant` requirement at specific axioms, surfacing precisely
which kernel behavior breaks reproducibility.

## What this demo does NOT claim

  *  Determinism across hardware / kernel implementations.  The
     claim is internal to *this* spec.  Vendor BLAS routines
     routinely choose reduction-tree shapes via heuristics keyed
     on input dimensions; if such a heuristic depends on the batch
     dimension, the same math runs through a different tree and
     produces different bits.  Bridging to silicon would need a
     reference implementation, an equivalence proof against a
     vendor kernel at a fixed config, and a runtime-config-stability
     proof — three separate research tasks.

  *  Anything about KV-cache or prefix sharing.  Different problem.

## Module layout

  *  `Demo.BatchInvariance.Forward`         — `Layer`, `TwoLayerBlock`,
                                                `RowLocal` predicate,
                                                generic forward
                                                composition lemmas.
  *  `Demo.BatchInvariance.Backward`        — `LayerBwd`, `WeightGrad.
                                                perSample` /
                                                `perSampleBatch` /
                                                `aggregate`,
                                                `RowLocal2` predicate.
  *  `Demo.BatchInvariance.TransformerBlock` — toy 4-step block (RMSNorm
                                                → linear → softmax →
                                                linear) with
                                                end-to-end batch
                                                invariance proved.
  *  `Demo.BatchInvariance.Backend`         — `Backend` / `BatchInvariant`
                                                typeclasses; per-op
                                                axiom that the batched
                                                primitive equals the
                                                row reference applied
                                                to the b-th input.
  *  `Demo.BatchInvariance.Backend.MX`      — the friendly reference
                                                instance.  Every axiom
                                                discharges by `rfl`.
  *  `Demo.BatchInvariance.Model`           — the toy LLM
                                                (`ToyLLM`), forward-pass
                                                routing through the
                                                `Backend`, and the
                                                forward-pass batch-
                                                invariance theorem
                                                `forwardBatch_eq_forwardRow`
                                                plus its permutation
                                                corollary.

## The headline

`toyLLM_batch_invariant` (below) bundles all five claims into a
single conjunction.  The individual theorems live in
`Demo.BatchInvariance.Model` (forward, input gradient, weight
gradient, plus permutation versions of each); this file's
contribution is the `super duper clear top-level statement`. -/

namespace Demo.BatchInvariance
open Demo.BatchInvariance.Model MX

/-- ## Batch invariance of the toy LLM (forward, backward, and order)

For any backend `α` satisfying the `BatchInvariant` interface, any
toy LLM `M`, any batch of `B` tokens, any upstream gradient
`dLogit`, any batch position `b`, and any permutation `σ` of the
batch:

  (1) Forward at row `b` equals the singleton forward.
  (2) Input gradient at row `b` equals the singleton input gradient.
  (3) Per-example parameter-gradient contribution at row `b`
      equals the singleton parameter gradient.
  (4) Permuting the batch permutes the forward output likewise.
  (5) Permuting the batch permutes the gradients likewise.

Bitwise — every `=` is at the FP-encoding level, not modulo ε.

The hostile-backend story:  this theorem holds for *any*
`Backend α` that comes with a `BatchInvariant α` instance.
Future hostile backends modelling cuBLAS-style split-K with batch-
dependent split factor, tensor-core mixed-precision accumulation,
atomic-add nondeterminism, or FMA fusion are expected to *fail*
the `BatchInvariant` axioms (or satisfy them only under
restrictions).  When such a backend is plugged in, this theorem
either does not apply (no `BatchInvariant` instance) or applies
under the restrictions stated by the hostile backend's instance —
making the gap between "math we proved" and "what the silicon
runs" precise and inspectable. -/
theorem toyLLM_batch_invariant
    {α : Type} [Backend α] [BatchInvariant α]
    {V K m : Nat} (M : ToyLLM α V K m)
    (LB : Backward.LayerBwd α K m V)
    (decodeX : MXVec K m → Fin (K * m) → α) (mulOp : α → α → α)
    {B : Nat} (tokens : Fin B → Fin V) (dLogit : Fin B → Fin V → α)
    (b : Fin B) (v : Fin V) (i : Fin (K * m))
    (σ : Equiv.Perm (Fin B)) :
    -- (1) forward batch invariance
    M.forwardBatch tokens b v = M.forwardRow (tokens b) v
  ∧ -- (2) input gradient batch invariance
    M.gradHiddenBatch LB tokens dLogit b i =
      M.gradHiddenRow LB (tokens b) (dLogit b) i
  ∧ -- (3) per-example weight gradient batch invariance
    M.weightGradBatch LB decodeX mulOp tokens dLogit b v i =
      M.weightGradRow LB decodeX mulOp (tokens b) (dLogit b) v i
  ∧ -- (4) forward permutation invariance
    M.forwardBatch (tokens ∘ σ) b v = M.forwardBatch tokens (σ b) v
  ∧ -- (5a) input gradient permutation invariance
    M.gradHiddenBatch LB (tokens ∘ σ) (dLogit ∘ σ) b i =
      M.gradHiddenBatch LB tokens dLogit (σ b) i
  ∧ -- (5b) weight gradient permutation invariance
    M.weightGradBatch LB decodeX mulOp (tokens ∘ σ) (dLogit ∘ σ) b v i =
      M.weightGradBatch LB decodeX mulOp tokens dLogit (σ b) v i :=
  ⟨ M.forwardBatch_eq_forwardRow tokens b v
  , M.gradHiddenBatch_eq_gradHiddenRow LB tokens dLogit b i
  , M.weightGradBatch_eq_weightGradRow LB decodeX mulOp tokens dLogit b v i
  , M.forwardBatch_permute tokens σ b v
  , M.gradHiddenBatch_permute LB tokens dLogit σ b i
  , M.weightGradBatch_permute LB decodeX mulOp tokens dLogit σ b v i ⟩

/-! ## Closed-form: batch invariance under the friendly MX backend

The capstone above is parametric in `[Backend α] [BatchInvariant α]`.
With the friendly `MXBackend` instances supplied automatically by
typeclass resolution, the theorem applies *unconditionally* at any
accumulator type `α`.  We restate it here without the typeclass
parameters as an explicit, closed-form claim — the answer to "is
this toy LLM, run on the MX kernels as currently specified, batch-
invariant?" is yes, and *this* is the named statement of that. -/

/-- **Batch invariance of the toy LLM under the MX backend.**
    Same five conjuncts as `toyLLM_batch_invariant`, but stated
    without the `[Backend α] [BatchInvariant α]` hypotheses — those
    are discharged by `instBackendMX` and `instBatchInvariantMX`.

    In particular: at `α = IEEEFloat 8 23` (FP32) — or any other
    accumulator type — the MX-backed toy LLM's per-batch-position
    forward output, input gradient, and per-example weight-gradient
    contribution are bitwise functions of that single position's
    input.  Reordering the batch reorders the outputs likewise. -/
theorem toyLLM_batch_invariant_MX
    {α : Type} {V K m : Nat} (M : Demo.BatchInvariance.Model.ToyLLM α V K m)
    (LB : Demo.BatchInvariance.Backward.LayerBwd α K m V)
    (decodeX : MX.MXVec K m → Fin (K * m) → α) (mulOp : α → α → α)
    {B : Nat} (tokens : Fin B → Fin V) (dLogit : Fin B → Fin V → α)
    (b : Fin B) (v : Fin V) (i : Fin (K * m))
    (σ : Equiv.Perm (Fin B)) :
    M.forwardBatch tokens b v = M.forwardRow (tokens b) v
  ∧ M.gradHiddenBatch LB tokens dLogit b i =
      M.gradHiddenRow LB (tokens b) (dLogit b) i
  ∧ M.weightGradBatch LB decodeX mulOp tokens dLogit b v i =
      M.weightGradRow LB decodeX mulOp (tokens b) (dLogit b) v i
  ∧ M.forwardBatch (tokens ∘ σ) b v = M.forwardBatch tokens (σ b) v
  ∧ M.gradHiddenBatch LB (tokens ∘ σ) (dLogit ∘ σ) b i =
      M.gradHiddenBatch LB tokens dLogit (σ b) i
  ∧ M.weightGradBatch LB decodeX mulOp (tokens ∘ σ) (dLogit ∘ σ) b v i =
      M.weightGradBatch LB decodeX mulOp tokens dLogit (σ b) v i :=
  toyLLM_batch_invariant M LB decodeX mulOp tokens dLogit b v i σ

end Demo.BatchInvariance
