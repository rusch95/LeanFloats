import Mathlib.Analysis.SpecialFunctions.Sqrt
import IEEEFloat.Round

/-! # Correctly-rounded arithmetic — IEEE 754 §6 specification

This module captures the IEEE 754 §6 contracts for the four basic
arithmetic operations (`+`, `−`, `×`, `÷`) at the spec level.  Each
contract is a structure with one field per case the standard pins
down explicitly:

  *  NaN propagation (§6.2): any NaN input yields a NaN result.
  *  Infinity arithmetic (§6.1):
       -  `(+∞) + (−∞)` is NaN; same-sign sum is that ∞.
       -  `0 × ±∞` and `±∞ × 0` are NaN.
       -  `±∞ ÷ ±∞` and `0 ÷ 0` are NaN.
       -  `finite ÷ 0` is ±∞ with the sign-xor of the operands.
       -  `finite ÷ ±∞` is signed zero.
  *  Finite operands: `z` is the RNE of the exact real-valued
     result (per `IEEEFloat.IsRoundedToNearestEven`).

The structures are spec-only: no constructive `add`, `sub`, `mul`,
`div` is provided here.  A constructive backend that satisfies these
contracts lands in a follow-up commit.  Until then, theorems about
specific kernels can be stated `∀ ⦃add⦄, IsCorrectlyRoundedAdd … → …`
in the same style as the WGSL repo's `[FloatSpec F]` carrier.
-/

namespace IEEEFloat

variable {eb mb : Nat}

/-! ## Addition `a + b = z` -/

structure IsCorrectlyRoundedAdd (a b z : IEEEFloat eb mb) : Prop where
  /-- NaN propagation. -/
  nan_prop : a = .nan ∨ b = .nan → z = .nan
  /-- `+∞ + −∞ = NaN`. -/
  inf_minus_inf :
    a.isInf = true → b.isInf = true → a.signBit ≠ b.signBit → z = .nan
  /-- Same-sign infinity sum is that infinity. -/
  inf_same_sign :
    a.isInf = true → b.isInf = true → a.signBit = b.signBit → z = a
  /-- `±∞ + finite = ±∞`. -/
  inf_left  : a.isInf = true → b.isFinite = true → z = a
  /-- `finite + ±∞ = ±∞`. -/
  inf_right : a.isFinite = true → b.isInf = true → z = b
  /-- Finite operands: `z` is RNE of the exact real sum. -/
  rne_of_sum : ∀ ra rb,
    a.toReal = some ra → b.toReal = some rb →
      IsRoundedToNearestEven (ra + rb) z

/-! ## Subtraction `a − b = z` -/

structure IsCorrectlyRoundedSub (a b z : IEEEFloat eb mb) : Prop where
  nan_prop : a = .nan ∨ b = .nan → z = .nan
  /-- `±∞ − ±∞` (same sign) is NaN. -/
  inf_same_sign :
    a.isInf = true → b.isInf = true → a.signBit = b.signBit → z = .nan
  /-- `±∞ − ∓∞` is the first operand. -/
  inf_diff_sign :
    a.isInf = true → b.isInf = true → a.signBit ≠ b.signBit → z = a
  inf_left  : a.isInf = true → b.isFinite = true → z = a
  /-- `finite − ±∞ = ∓∞` (sign flip). -/
  inf_right : a.isFinite = true → b.isInf = true → z = -b
  rne_of_diff : ∀ ra rb,
    a.toReal = some ra → b.toReal = some rb →
      IsRoundedToNearestEven (ra - rb) z

/-! ## Multiplication `a · b = z` -/

structure IsCorrectlyRoundedMul (a b z : IEEEFloat eb mb) : Prop where
  nan_prop : a = .nan ∨ b = .nan → z = .nan
  /-- `0 · ±∞` and `±∞ · 0` are NaN. -/
  zero_times_inf :
    (a.isZero = true ∧ b.isInf = true) ∨
    (a.isInf = true ∧ b.isZero = true) → z = .nan
  /-- `±∞ · finite_nonzero = ±∞` (sign-xor). -/
  inf_times_finite :
    a.isInf = true → b.isFinite = true → b.isZero = false →
      z = .inf (a.signBit != b.signBit)
  finite_times_inf :
    a.isFinite = true → a.isZero = false → b.isInf = true →
      z = .inf (a.signBit != b.signBit)
  /-- `±∞ · ±∞ = ±∞` (sign-xor). -/
  inf_times_inf :
    a.isInf = true → b.isInf = true →
      z = .inf (a.signBit != b.signBit)
  rne_of_product : ∀ ra rb,
    a.toReal = some ra → b.toReal = some rb →
      IsRoundedToNearestEven (ra * rb) z

/-! ## Square root `√a = z` -/

structure IsCorrectlyRoundedSqrt (a z : IEEEFloat eb mb) : Prop where
  /-- NaN propagation. -/
  nan_prop : a = .nan → z = .nan
  /-- `√(±0) = ±0` (sign preserved per IEEE 754 §6.3). -/
  sqrt_zero : a.isZero = true → z = a
  /-- `√(+∞) = +∞`. -/
  sqrt_pos_inf : a = .inf false → z = .inf false
  /-- `√(−∞) = NaN`. -/
  sqrt_neg_inf : a = .inf true → z = .nan
  /-- `√(negative nonzero)` = NaN (invalid operation). -/
  sqrt_negative :
    a.isFinite = true → a.isZero = false → a.signBit = true → z = .nan
  /-- For positive finite operands: `z` is RNE of `√a` over the reals.
      The `0 < ra` requirement separates this from the `sqrt_zero`
      case (which directly pins `z = a`). -/
  rne_of_sqrt : ∀ ra,
    a.toReal = some ra → 0 < ra → IsRoundedToNearestEven (Real.sqrt ra) z

/-! ## Fused multiply-add `a · b + c = z` (single rounding) -/

/-- "Multiply `a × b` would produce ±∞ in extended-real arithmetic"
    — at least one operand is infinite, and the other is finite and nonzero
    (or both infinite). -/
def MultProducesInf (a b : IEEEFloat eb mb) : Prop :=
  (a.isInf = true ∧ b.isInf = true) ∨
  (a.isInf = true ∧ b.isFinite = true ∧ b.isZero = false) ∨
  (a.isFinite = true ∧ a.isZero = false ∧ b.isInf = true)

structure IsCorrectlyRoundedFma (a b c z : IEEEFloat eb mb) : Prop where
  /-- NaN propagation: any NaN input forces a NaN result. -/
  nan_prop : a = .nan ∨ b = .nan ∨ c = .nan → z = .nan
  /-- Invalid multiply: `0 × ±∞` or `±∞ × 0` → NaN, regardless of `c`. -/
  zero_times_inf :
    (a.isZero = true ∧ b.isInf = true) ∨
    (a.isInf = true ∧ b.isZero = true) → z = .nan
  /-- `(a×b is ±∞) + (c is ±∞, matching sign)` → ±∞. -/
  inf_mult_inf_match :
    MultProducesInf a b → c.isInf = true →
    (a.signBit != b.signBit) = c.signBit →
    z = .inf c.signBit
  /-- `(a×b is ±∞) + (c is ±∞, opposite sign)` → NaN. -/
  inf_mult_inf_diff :
    MultProducesInf a b → c.isInf = true →
    (a.signBit != b.signBit) ≠ c.signBit →
    z = .nan
  /-- `(a×b is ±∞) + (c finite)` → ±∞ with sign-xor of multiplicands. -/
  inf_mult_finite :
    MultProducesInf a b → c.isFinite = true →
    z = .inf (a.signBit != b.signBit)
  /-- `(a, b finite) + (c is ±∞)` → c. -/
  finite_finite_inf :
    a.isFinite = true → b.isFinite = true → c.isInf = true → z = c
  /-- All finite operands: `z` is RNE of the exact real `a×b + c`. -/
  rne_of_fma : ∀ ra rb rc,
    a.toReal = some ra → b.toReal = some rb → c.toReal = some rc →
      IsRoundedToNearestEven (ra * rb + rc) z

/-! ## Division `a / b = z` -/

structure IsCorrectlyRoundedDiv (a b z : IEEEFloat eb mb) : Prop where
  nan_prop : a = .nan ∨ b = .nan → z = .nan
  /-- `0 / 0` is NaN. -/
  zero_div_zero : a.isZero = true → b.isZero = true → z = .nan
  /-- `±∞ / ±∞` is NaN. -/
  inf_div_inf : a.isInf = true → b.isInf = true → z = .nan
  /-- `finite_nonzero / 0 = ±∞` (sign-xor). -/
  finite_div_zero :
    a.isFinite = true → a.isZero = false → b.isZero = true →
      z = .inf (a.signBit != b.signBit)
  /-- `±∞ / finite_nonzero = ±∞` (sign-xor). -/
  inf_div_finite :
    a.isInf = true → b.isFinite = true → b.isZero = false →
      z = .inf (a.signBit != b.signBit)
  /-- `finite / ±∞ = ±0` (sign-xor). -/
  finite_div_inf :
    a.isFinite = true → b.isInf = true →
      z.isZero = true ∧ z.signBit = (a.signBit != b.signBit)
  rne_of_quotient : ∀ ra rb,
    a.toReal = some ra → b.toReal = some rb → rb ≠ 0 →
      IsRoundedToNearestEven (ra / rb) z

end IEEEFloat
