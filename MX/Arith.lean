import MX.Round
import MX.E8M0

/-! # Correctly-rounded arithmetic — spec predicates for E2M1

Mirrors `IEEEFloat.Arith`.  Substantially simpler because E2M1 has
*no NaN and no Inf* at the element level.  Out-of-range results
saturate to `±6` (per the OCP MXFP4 spec); `IsRoundedToNearestEven`
already encodes this saturation, so the arithmetic specs reduce to a
single line: "the result is RNE of the exact real-valued operation."

## Why specs at all?

The OCP MX specification doesn't define element-level arithmetic on
E2M1 — real workloads dequantize to FP32 (or higher), do the
arithmetic there, and re-quantize on output.  So `add : E2M1 → E2M1
→ E2M1` is a synthetic concept.  We define it for two reasons:

  1. **Symmetry with IEEEFloat.**  Downstream proofs that need a
     uniform "add at format X" interface can dispatch on E2M1 as
     well as Binary32 / BFloat16 / etc.  This is the WGSL-repo's
     `[FloatSpec F]` pattern applied here.

  2. **A test-bed for the rounding contract.**  E2M1 has only 16
     values, so theorems about correctly-rounded arithmetic are
     fully decidable by exhaustive case analysis.  This makes E2M1
     a tractable warm-up before tackling the same theorems for
     wider IEEE formats.

## Division: zero handling

E2M1 has no Inf to round to, so division by zero must saturate.  We
adopt:

  *  `0 / 0 = +0`.  No `NaN` in the format; choosing `+0` instead of
     a sentinel keeps the result well-typed.  This is a design
     choice — alternatives are `-0` or "raise an exception" (we have
     no exception machinery here), but `+0` is the simplest.
  *  `nonzero / 0 = ±6` (sign-xor).  Saturate to the maximum
     representable, with sign as in IEEE 754 §6.1.

These are minor design choices that downstream callers of E2M1
arithmetic can override by re-deriving the constructive backend.
-/

namespace MX
namespace E2M1

/-! ## Addition `a + b = z` -/

/-- E2M1 addition: `z` is the RNE-saturating round of the exact real
    sum `a.toReal + b.toReal`.  No NaN/Inf cases — every input is a
    finite real, and the result saturates at `±6`. -/
structure IsCorrectlyRoundedAdd (a b z : E2M1) : Prop where
  rne_of_sum : IsRoundedToNearestEven (a.toReal + b.toReal) z

/-! ## Subtraction `a − b = z` -/

structure IsCorrectlyRoundedSub (a b z : E2M1) : Prop where
  rne_of_diff : IsRoundedToNearestEven (a.toReal - b.toReal) z

/-! ## Multiplication `a · b = z` -/

structure IsCorrectlyRoundedMul (a b z : E2M1) : Prop where
  rne_of_product : IsRoundedToNearestEven (a.toReal * b.toReal) z

/-! ## Fused multiply-add `a · b + c = z` (single rounding) -/

structure IsCorrectlyRoundedFma (a b c z : E2M1) : Prop where
  rne_of_fma : IsRoundedToNearestEven (a.toReal * b.toReal + c.toReal) z

/-! ## Division `a / b = z`

The only nontrivial case at the spec level: division by zero, which
saturates rather than producing `±Inf` (E2M1 has no Inf). -/

/-- E2M1 division spec.  Three cases:

      *  `0 / 0`           — `z = +0` (design choice; see module docstring).
      *  `nonzero / 0`     — `z = ±6` saturating, sign-xor.
      *  `_ / nonzero`     — `z = roundRNE (a.toReal / b.toReal)`. -/
structure IsCorrectlyRoundedDiv (a b z : E2M1) : Prop where
  zero_div_zero : a.isZero = true → b.isZero = true → z = ⟨false, 0, 0⟩
  finite_div_zero :
    b.isZero = true → a.isZero = false →
      z = ⟨decide (a.s ≠ b.s), 3, 1⟩
  rne_of_quotient :
    b.isZero = false → IsRoundedToNearestEven (a.toReal / b.toReal) z

end E2M1

namespace E8M0

/-! # Correctly-rounded scale multiplication for E8M0

The natural arithmetic on E8M0 is *multiplication* (since values are
of the form `2^k`, multiplication is exponent addition).  Used in
block-block products: `(s_a · s_b)` is itself an E8M0-like scale, and
hardware can compute it directly without going through `Real`.

Saturation: `2^a · 2^b = 2^(a+b)`, but if `a + b ∉ [-127, 127]`, we
saturate to the boundary.  NaN propagation: any NaN operand produces
NaN.  Result is *not* rounded — it's exact when in range.
-/

/-- E8M0 multiplication spec.  Closed under multiplication except at
    the saturating boundaries; NaN-propagating. -/
structure IsCorrectlyMul (a b z : E8M0) : Prop where
  /-- NaN propagation: any NaN operand produces NaN. -/
  nan_prop : a.isNaN = true ∨ b.isNaN = true → z = nan
  /-- For non-NaN operands whose exponent sum is in range:
      `z = 2^(exp_a + exp_b)`.  Encoding-level: the result's raw is
      `a.raw + b.raw - 127`.  We require `a.raw + b.raw ≥ 127` (so the
      subtracted exponent doesn't underflow) and `a.raw + b.raw < 382`
      (so it doesn't overflow `Fin 256` after subtracting bias). -/
  in_range :
    a.isNaN = false → b.isNaN = false →
    127 ≤ a.raw.val + b.raw.val → a.raw.val + b.raw.val < 127 + 254 →
    z.raw.val = a.raw.val + b.raw.val - 127

/-! ## Inverse: `1 / s` for E8M0

For `s = 2^k` (non-NaN), `1/s = 2^(-k)`.  Encoding-level: invert
around the bias, `(254 - raw) = bias - (raw - bias)`.  Saturating
boundaries: `1 / 2^127 = 2^(-127)` (i.e., raw 0); `1 / 2^(-127) = 2^127`
(raw 254).  NaN → NaN. -/

/-- E8M0 reciprocal spec. -/
structure IsCorrectlyInv (a z : E8M0) : Prop where
  nan_prop : a.isNaN = true → z = nan
  /-- For non-NaN: `z.raw = 254 - a.raw`, the bias-symmetric reflection. -/
  reflect :
    a.isNaN = false → z.raw.val = 254 - a.raw.val

end E8M0
end MX
