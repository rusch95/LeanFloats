import MX.E2M1
import MX.E8M0
import MX.Block
import MX.Decode
import MX.Round
import MX.Encode
import MX.Ops
import MX.Compare
import MX.Arith
import MX.Backend
import MX.Bits
import MX.Kernel
import MX.MXFP4_FP32
import MX.Quantize
import MX.Dot
import MX.Reduction
import MX.GEMM
import MX.GEMM_FP32
import MX.TreeDependence
import MX.RMSNorm
import MX.Softmax

/-! # MXFP4 — OCP Microscaling FP4 (block-scaled 4-bit float)

A formalization of the OCP Microscaling specification v1.0, MXFP4
variant.  Distinct from `IEEEFloat` because:

  *  **No Inf, no NaN** at the element level.  All 16 bit patterns
     of the 4-bit `E2M1` element decode to finite real values.
  *  **Block structure.**  K=32 elements share one E8M0 scale.  The
     scale CAN be NaN (its all-ones bit pattern), which tags the
     whole block as NaN.
  *  **Saturating rounding.**  Out-of-range values round to ±max,
     not to ±∞ (because ±∞ doesn't exist).

## Structure

  *  `MX.E2M1`   — the 4-bit element type.  16 distinct values
                   `{0, ±0.5, ±1, ±1.5, ±2, ±3, ±4, ±6}`.
  *  `MX.E8M0`   — the 8-bit scale type: `2^k` for `k ∈ [-127, 127]`,
                   plus a single NaN pattern.
  *  `MX.Block`  — a block of 32 `E2M1` values plus an `E8M0` scale.
  *  `MX.Decode` — `MXBlock → Vector 32 (Option ℝ)` (None when the
                   block is NaN).

## Relationship to `IEEEFloat`

The two libraries share *concept* — sign + biased exponent + trailing
mantissa, the standard formula `(1 + m/2^mb) · 2^(e-bias)` for normals
and `(m/2^mb) · 2^(1-bias)` for subnormals — but **not implementation**:

  *  `IEEEFloat eb mb` is an inductive type with explicit `nan`,
     `inf`, `finite` constructors, where `finite` uses
     `Fin (2^eb - 1)` to exclude the reserved all-ones exponent.
  *  `E2M1` is a `BitVec 4` (or equivalent), where every pattern is
     a valid finite value.  No reserved exponents.

A future common typeclass `[BinaryFloatFormat]` may abstract over
both — see the discussion in `MX/Block.lean`.  We resist designing
it speculatively until both libraries have enough downstream usage
to dictate the right shape.

## OCP MX v1.0 reference

  Open Compute Project, "Microscaling Formats (MX) Specification,
  Version 1.0" (Sept 2023).  The MXFP4 element format is E2M1, the
  scale format is E8M0, the block size is K=32.
-/
