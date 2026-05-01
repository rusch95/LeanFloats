import Demo.BatchInvariance.Forward
import Demo.BatchInvariance.Backward
import Demo.BatchInvariance.TransformerBlock

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
                                                typeclasses (forthcoming).
  *  `Demo.BatchInvariance.Backend.MX`      — concrete `MXBackend`
                                                instance (forthcoming).
  *  `Demo.BatchInvariance.Model`           — toy LLM definition
                                                (forthcoming).

The headline theorem will land in this file once the backend
abstraction and the toy LLM are in place. -/
