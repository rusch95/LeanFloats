import MX.GEMM
import IEEEFloat.RoundExistence
import IEEEFloat.Formats
import IEEEFloat.Backend

/-! # MX-GEMM with an FP32 outer accumulator (bit-level batch invariance)

Specialization of `mxGEMMAcc` (`MX/GEMM.lean`) to `Acc := Binary32`
(`IEEEFloat 8 23`) with IEEE 754 §4.3.1 nearest-even rounding.

This is the form an inference engineer cites: "MX-GEMM with an FP32
outer accumulator is bit-deterministic — the output at row `b` is a
function of `(A.row b, Wt)` and the kernel's reduction tree alone,
independent of how the batcher groups requests."

The substantive content was already proved in
`mxGEMMAcc_batch_invariant`.  This module is the one-line
specialization plus the standard rounding function — no new proof
obligations, but stated in concrete IEEE FP32 terms so downstream
consumers don't have to plumb the `Acc` parameter themselves.

## What this does NOT prove

  *  Tree-irrelevance over FP32 — it's *false* in general, and that
     failure is exactly what makes batch invariance non-trivial.  A
     constructive counterexample (two valid sum-trees that disagree
     on a specific FP32 input) is the natural follow-up; see the
     `mxGEMM_tree_irrelevant_over_reals` ℝ-side counterpart in
     `MX/GEMM.lean` for the spec it would falsify.

  *  Inner-block exactness — the claim that `MXBlock.blockDot` lifted
     to an FP32 accumulator equals its `ℝ` value bit-exactly.  True
     for MXFP4 (E2M1 elements have ≤3 mantissa bits, products ≤5
     bits, 32 sums fit in FP32 with no rounding) but proved
     elsewhere; this module assumes block products enter the
     accumulator exactly via `roundFP32` of the `ℝ`-valued
     `blockDot`.
-/

namespace MX

/-- Round-to-nearest-even into FP32 (`Binary32` = `IEEEFloat 8 23`).
    Discharges the `1 ≤ eb` / `1 ≤ mb` side conditions of
    `IEEEFloat.roundToNearestEven` for the FP32 widths by `decide`. -/
noncomputable def roundFP32 : ℝ → IEEEFloat 8 23 :=
  IEEEFloat.roundToNearestEven (eb := 8) (mb := 23) (by decide) (by decide)

/-- IEEE 754 RNE addition over FP32.  The `1 ≤ eb` / `1 ≤ mb`
    side conditions of `IEEEFloat.add` are discharged for the FP32
    widths.  Used both as the per-block reducer in concrete kernel
    instantiations and as the witness type for fp non-associativity
    in `MX/TreeDependence.lean`. -/
noncomputable def addFP32 : IEEEFloat 8 23 → IEEEFloat 8 23 → IEEEFloat 8 23 :=
  IEEEFloat.add (eb := 8) (mb := 23) (by decide) (by decide)

variable {B N K m : Nat}

/-- The MX-GEMM with an FP32 outer accumulator and RNE rounding of
    each block product.  Block products are computed exactly in `ℝ`
    via `MXBlock.blockDot`, rounded into FP32 once per block, and
    then combined by the kernel's reduction tree `t`. -/
noncomputable def mxGEMM_FP32
    (t : ReductionTree (IEEEFloat 8 23) m)
    (A : MXMatrix B K m) (Wt : MXMatrix N K m)
    (b : Fin B) (n : Fin N) : IEEEFloat 8 23 :=
  mxGEMMAcc roundFP32 t A Wt b n

/-- **Bit-level batch invariance for FP32-accumulator MX-GEMM.**

    For any fixed reduction tree `t : ReductionTree Binary32 m`
    (depending only on the contraction dimension `m = K_total / 32`),
    the GEMM output at row `b` is *bit-equal* across any two batches
    that share that row.  Direct specialization of
    `mxGEMMAcc_batch_invariant` to `Acc := IEEEFloat 8 23` and
    `round := roundFP32`.

    This is the formal counterpart to the Thinking Machines blog
    post's central claim that LLM inference becomes deterministic
    iff the kernel commits to a reduction tree that depends only on
    the contraction dimension. -/
theorem mxGEMM_FP32_batch_invariant
    (t : ReductionTree (IEEEFloat 8 23) m)
    (A A' : MXMatrix B K m) (Wt : MXMatrix N K m)
    (b : Fin B) (n : Fin N) (h : A.get b = A'.get b) :
    mxGEMM_FP32 t A Wt b n = mxGEMM_FP32 t A' Wt b n :=
  mxGEMMAcc_batch_invariant roundFP32 t A A' Wt b n h

/-- Blockwise form: per-block agreement at row `b` suffices. -/
theorem mxGEMM_FP32_batch_invariant_blockwise
    (t : ReductionTree (IEEEFloat 8 23) m)
    (A A' : MXMatrix B K m) (Wt : MXMatrix N K m)
    (b : Fin B) (n : Fin N)
    (h : ∀ j : Fin m, (A.get b).get j = (A'.get b).get j) :
    mxGEMM_FP32 t A Wt b n = mxGEMM_FP32 t A' Wt b n :=
  mxGEMMAcc_batch_invariant_blockwise roundFP32 t A A' Wt b n h

/-- End-to-end batch invariance: encode-then-FP32-GEMM is row-local. -/
theorem encode_then_mxGEMM_FP32_batch_invariant
    (t : ReductionTree (IEEEFloat 8 23) m)
    (A A' : MatReal B K m) (Wt : MXMatrix N K m)
    (b : Fin B) (n : Fin N) (h : A.get b = A'.get b) :
    mxGEMM_FP32 t (MXVec.encodeMatrix A) Wt b n =
      mxGEMM_FP32 t (MXVec.encodeMatrix A') Wt b n :=
  encode_then_mxGEMMAcc_batch_invariant roundFP32 t A A' Wt b n h

end MX
