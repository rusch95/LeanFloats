import Demo.BatchInvariance.Backend

/-! # The reference `MXBackend`

The friendly backend: every batched primitive is *defined* by
applying the canonical per-row reference to each row in isolation,
so the `BatchInvariant` axioms discharge by `rfl`.

This is the baseline against which future hostile backends will be
compared.  It models "the kernels exactly as specified in `MX/`",
with no implementation tricks beyond what the spec already encodes
(reduction-tree shape committed to `m`, no cross-batch coupling).

For any accumulator type `α`, this provides:

  *  `Backend α` instance with all `*Batch` ops as `*ApplyBatch`
     compositions of per-row references.
  *  `BatchInvariant α` instance — every axiom is `rfl`. -/

namespace Demo.BatchInvariance
open MX

/-- The reference `Backend` instance: friendly, with no cross-batch
    coupling.  Each batched op equals the per-row apply lifted by
    `fun X b => apply (X.get b)`. -/
instance instBackendMX (α : Type) : Backend α where
  layerApplyBatch L X b n :=
    Forward.Layer.applyBatch L X b n
  layerBwdApplyBatch LB X dY b i :=
    Backward.LayerBwd.applyBatch LB X dY b i
  weightGradPerSampleBatch LB decodeX mulOp X dY b n i :=
    Backward.WeightGrad.perSampleBatch LB decodeX mulOp X dY b n i

/-- The reference `MXBackend` is batch-invariant — by construction.
    Each axiom holds by definitional equality:

      `layerApplyBatch L X b n`
        ≡ `L.applyBatch X b n`         -- definition of MXBackend
        ≡ `L.apply (X.get b) n`        -- definition of Layer.applyBatch

    and similarly for backward and weight-gradient. -/
instance instBatchInvariantMX (α : Type) : BatchInvariant α where
  layer_batch_eq_apply _ _ _ _ := rfl
  layerBwd_batch_eq_apply _ _ _ _ _ := rfl
  weightGrad_batch_eq_apply _ _ _ _ _ _ _ _ := rfl

end Demo.BatchInvariance
