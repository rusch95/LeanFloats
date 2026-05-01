import IEEEFloat.UlpBound
import IEEEFloat.Backend

/-! # Error-bound lemmas for correctly-rounded operations

A practical wrapper layer over `UlpBound`'s half-ULP theorem and
`Backend`'s `IsCorrectlyRounded*` contracts.  Each lemma here is a
named handle for a frequently-recurring fact in floating-point
error analysis.

  *  `unitRoundoff eb mb := 2^{-mb-1}` — the "u" of standard texts
     (Higham, *Accuracy and Stability of Numerical Algorithms*).
     Half a ULP relative to a normalised significand, hence the
     name.
  *  `machineEpsilon eb mb := 2^{-mb}` — the spacing between 1 and
     the next representable above 1.

  *  `add_within_half_ulp`, `sub_within_half_ulp`,
     `mul_within_half_ulp`, `div_within_half_ulp`,
     `fma_within_half_ulp` — for any operand pair (or triple) whose
     exact real result is in range, the rounded result is within
     half a ULP of the exact answer.

These are direct corollaries of `half_ulp_bound` plus the relevant
`IsCorrectlyRounded*` contract; downstream consumers should reach for
them before re-deriving the bounds in situ.

Beyond this module: relative-error bounds (in the `1 + ε` style),
Sterbenz exactness, and round monotonicity are intentionally left for
follow-up — each requires its own structural lemma about `ulp` /
`finiteValue` and is a project unto itself.
-/

namespace IEEEFloat

variable {eb mb : Nat}

/-! ## Machine constants -/

/-- IEEE 754 unit roundoff: `2^{-mb-1}`.  This is the standard
    numerical-analysis "u" — half a ULP relative to a normalised
    significand. -/
noncomputable def unitRoundoff (eb mb : Nat) : ℝ :=
  (2 : ℝ) ^ (-(mb : Int) - 1)

/-- Machine epsilon: `2^{-mb}`, the spacing between 1.0 and the
    next representable above 1.0. -/
noncomputable def machineEpsilon (eb mb : Nat) : ℝ :=
  (2 : ℝ) ^ (-(mb : Int))

/-- `unitRoundoff = machineEpsilon / 2`. -/
theorem unitRoundoff_eq_half_machineEpsilon :
    unitRoundoff eb mb = machineEpsilon eb mb / 2 := by
  unfold unitRoundoff machineEpsilon
  rw [show (-(mb : Int) - 1 : Int) = -(mb : Int) + (-1) from by ring]
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-! ## Half-ULP bounds for the correctly-rounded operations

Each `*_within_half_ulp` theorem says: for finite operands whose
exact real result is in range, the corresponding `Backend`
operation produces a result within half a ULP of the exact answer.
-/

/-- The generic half-ULP bound for an operation: any value `z`
    satisfying `IsRoundedToNearestEven r z` lies within `z.ulp / 2`
    of `r`. -/
theorem rne_within_half_ulp
    (heb : 2 ≤ eb) (hmb : 1 ≤ mb)
    (r : ℝ) (z : IEEEFloat eb mb)
    (h_rne : IsRoundedToNearestEven r z)
    (hover : |r| < overflowBoundary eb mb) :
    |r - z.toRealOrZero| ≤ z.ulp / 2 :=
  half_ulp_bound heb hmb r z (IsRoundedToNearest.of_rne h_rne) hover

/-- For finite operands `x`, `y` with `|x + y|` in range, the
    correctly-rounded `add` result is within half a ULP of the exact
    sum. -/
theorem add_within_half_ulp
    (heb : 2 ≤ eb) (hmb : 1 ≤ mb)
    (x y : IEEEFloat eb mb) (rx ry : ℝ)
    (hx : x.toReal = some rx) (hy : y.toReal = some ry)
    (hover : |rx + ry| < overflowBoundary eb mb) :
    let z := add (le_trans (by decide) heb) hmb x y
    |(rx + ry) - z.toRealOrZero| ≤ z.ulp / 2 := by
  intro z
  exact rne_within_half_ulp heb hmb (rx + ry) z
    ((add_isCorrectlyRounded _ _ x y).rne_of_sum rx ry hx hy) hover

/-- For finite operands `x`, `y` with `|x - y|` in range, the
    correctly-rounded `sub` result is within half a ULP of the exact
    difference. -/
theorem sub_within_half_ulp
    (heb : 2 ≤ eb) (hmb : 1 ≤ mb)
    (x y : IEEEFloat eb mb) (rx ry : ℝ)
    (hx : x.toReal = some rx) (hy : y.toReal = some ry)
    (hover : |rx - ry| < overflowBoundary eb mb) :
    let z := sub (le_trans (by decide) heb) hmb x y
    |(rx - ry) - z.toRealOrZero| ≤ z.ulp / 2 := by
  intro z
  exact rne_within_half_ulp heb hmb (rx - ry) z
    ((sub_isCorrectlyRounded _ _ x y).rne_of_diff rx ry hx hy) hover

/-- For finite operands `x`, `y` with `|x · y|` in range, the
    correctly-rounded `mul` result is within half a ULP of the exact
    product. -/
theorem mul_within_half_ulp
    (heb : 2 ≤ eb) (hmb : 1 ≤ mb)
    (x y : IEEEFloat eb mb) (rx ry : ℝ)
    (hx : x.toReal = some rx) (hy : y.toReal = some ry)
    (hover : |rx * ry| < overflowBoundary eb mb) :
    let z := mul (le_trans (by decide) heb) hmb x y
    |(rx * ry) - z.toRealOrZero| ≤ z.ulp / 2 := by
  intro z
  exact rne_within_half_ulp heb hmb (rx * ry) z
    ((mul_isCorrectlyRounded _ _ x y).rne_of_product rx ry hx hy) hover

/-- For finite operands `x`, `y` with `y ≠ 0` and `|x / y|` in
    range, the correctly-rounded `div` result is within half a ULP
    of the exact quotient. -/
theorem div_within_half_ulp
    (heb : 2 ≤ eb) (hmb : 1 ≤ mb)
    (x y : IEEEFloat eb mb) (rx ry : ℝ)
    (hx : x.toReal = some rx) (hy : y.toReal = some ry) (hry : ry ≠ 0)
    (hover : |rx / ry| < overflowBoundary eb mb) :
    let z := div (le_trans (by decide) heb) hmb x y
    |(rx / ry) - z.toRealOrZero| ≤ z.ulp / 2 := by
  intro z
  exact rne_within_half_ulp heb hmb (rx / ry) z
    ((div_isCorrectlyRounded _ _ x y).rne_of_quotient rx ry hx hy hry) hover

/-- For finite operands `a`, `b`, `c` with `|a · b + c|` in range,
    the correctly-rounded `fma` result is within half a ULP of the
    exact value (single rounding). -/
theorem fma_within_half_ulp
    (heb : 2 ≤ eb) (hmb : 1 ≤ mb)
    (a b c : IEEEFloat eb mb) (ra rb rc : ℝ)
    (ha : a.toReal = some ra) (hb : b.toReal = some rb) (hc : c.toReal = some rc)
    (hover : |ra * rb + rc| < overflowBoundary eb mb) :
    let z := fma (le_trans (by decide) heb) hmb a b c
    |(ra * rb + rc) - z.toRealOrZero| ≤ z.ulp / 2 := by
  intro z
  exact rne_within_half_ulp heb hmb (ra * rb + rc) z
    ((fma_isCorrectlyRounded _ _ a b c).rne_of_fma ra rb rc ha hb hc) hover

end IEEEFloat
