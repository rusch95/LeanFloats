import IEEEFloat.Basic
import IEEEFloat.Real
import IEEEFloat.Round
import IEEEFloat.RoundExistence
import IEEEFloat.Spacing
import IEEEFloat.Arith
import IEEEFloat.Formats
import IEEEFloat.UlpBound
import IEEEFloat.Bits
import IEEEFloat.Backend
import IEEEFloat.Ops
import IEEEFloat.Compare
import IEEEFloat.ErrorBounds
import IEEEFloat.Convert
import IEEEFloat.ConvertFormat
import IEEEFloat.RoundingMode
import IEEEFloat.Identities
import IEEEFloat.FloatSpec
import IEEEFloat.FloatSpec.F32
import IEEEFloat.FloatSpec.F16
import IEEEFloat.FloatSpec.BF16

/-! # IEEEFloat — strict IEEE 754 binary floating-point in Lean 4

This library formalizes the IEEE 754-2019 binary interchange formats
(`binary16`, `binary32`, `binary64`, plus `bfloat16` for ML use)
parameterized over exponent and mantissa widths.  Strict IEEE only —
no relaxations, no platform-specific quirks.  Downstream consumers
that need the WGSL §15.7 relaxed semantics, the C/LLVM `llvm.fmuladd`
contraction permission, or numpy-style alternative rounding modes
should layer those on top of the contracts established here.

## Module layout

  *  `IEEEFloat.Basic`    — the type, sign/exponent/mantissa carrier,
                            predicates (isNaN/isInf/isFinite/isZero/
                            isSubnormal/isNormal), `bias` / `maxExp` /
                            `minNormalExp` / `minSubnormalExp`, and
                            sign-flip negation.
  *  `IEEEFloat.Real`     — `finiteValue`, `toReal : F → Option ℝ`,
                            `Representable` predicate.  Bridges from
                            the bit-level encoding to `Mathlib`'s `ℝ`.
  *  `IEEEFloat.Round`    — `IsRoundedToNearestEven` (the IEEE 754 §4.3.1
                            `roundTiesToEven` spec), the weaker
                            `IsRoundedToNearest` (no tie-break), and
                            the format's real-valued boundaries
                            (`maxFinite`, `minPosSubnormal`, `topUlp`,
                            `overflowBoundary`).
  *  `IEEEFloat.RoundExistence` — classical existence of RN via
                            `Finset.exists_min_image`; defines
                            `roundToNearest := Classical.choose …`.
                            RNE existence (with even-mantissa
                            tie-break) is a follow-up.
  *  `IEEEFloat.Spacing`  — `ulp`, `nextFinite`, `prevFinite`.
                            Definitions only; real-value
                            monotonicity / adjacency / parity
                            alternation theorems land in follow-ups.
  *  `IEEEFloat.Arith`    — `IsCorrectlyRoundedAdd / Sub / Mul / Div`
                            structures encoding IEEE 754 §6 NaN
                            propagation, ±∞ rules, and "RNE of exact
                            real result" for finite operands.
  *  `IEEEFloat.Formats`  — `Binary16` / `Binary32` / `Binary64` /
                            `BFloat16` abbreviations.
  *  `IEEEFloat.UlpBound`  — half-ULP bound for any RN result in
                            range: `|r - x.toRealOrZero| ≤ x.ulp / 2`.
  *  `IEEEFloat.Bits`      — bit-pattern interchange:
                            `toBits : IEEEFloat eb mb → BitVec (1+eb+mb)`
                            and `fromBits` (canonicalising NaN), with
                            round-trip / injectivity proofs.
  *  `IEEEFloat.Backend`   — explicit `add` / `sub` / `mul` / `div`
                            (still `noncomputable` — `ℝ` is) plus
                            proofs they satisfy the
                            `IsCorrectlyRounded*` contracts.
  *  `IEEEFloat.Ops`       — `abs`, `copySign`, `fpclass` /
                            `FloatClass`.  Constructor-level (no
                            rounding); covers IEEE 754 §5.5 and §5.7.2.
  *  `IEEEFloat.Compare`   — `lt`, `le`, `eq`, `unordered` (§5.6) plus
                            `minimum` / `maximum` / `minimumNumber` /
                            `maximumNumber` (§5.3.1).  All
                            constructor-level and computable.
  *  `IEEEFloat.ErrorBounds` — practical wrappers building on
                            `UlpBound`: per-op half-ULP bounds for
                            `add`/`sub`/`mul`/`div`/`fma`,
                            `unitRoundoff`, `machineEpsilon`.
  *  `IEEEFloat.Convert`   — integer ↔ float conversions:
                            `convertFromInt`, `truncToInt`,
                            `floorToInt`, `ceilToInt`,
                            `roundToIntTiesAway`, `roundToIntTiesEven`.
  *  `IEEEFloat.ConvertFormat` — cross-format conversion between
                            different `(eb, mb)` widths (§5.4.2).
  *  `IEEEFloat.RoundingMode` — `RoundingMode` enum + per-mode
                            `IsRoundedTo*` predicates for all five
                            §4.3 directions (only RNE is constructive
                            so far; the others have specs only).

## Status

This is the **scaffolding** commit.  All definitions land; no
substantive theorems are proved yet.  In particular:

  *  No `bitcast` / `bitcastFloat32 : Float → IEEEFloat 8 23` shim —
     `Bits.lean` lands the bit-level encoding but the bridge to
     host-native floats (Lean's `Float`) is left for a follow-up
     `IEEEFloat.Host` module.

## Why a spec-only first cut?

Two reasons.  First, the predicates are what *clients* depend on —
ULP bounds, kernel-equivalence proofs, and the existing WGSL
`FloatSpec` typeclass all want a contract, not an implementation.
Landing the contract first lets dependent proofs proceed without
waiting for a constructive backend.  Second, the constructive
proofs (RNE existence with tie-breaking, NaN rules, signed-zero
bookkeeping) are the *interesting* mathematical content of an IEEE
754 formalization; we want them in their own commit with proper
attention rather than rolled into a scaffolding diff.
-/
