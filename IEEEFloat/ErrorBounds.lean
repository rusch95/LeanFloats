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
noncomputable def unitRoundoff (_eb mb : Nat) : ℝ :=
  (2 : ℝ) ^ (-(mb : Int) - 1)

/-- Machine epsilon: `2^{-mb}`, the spacing between 1.0 and the
    next representable above 1.0. -/
noncomputable def machineEpsilon (_eb mb : Nat) : ℝ :=
  (2 : ℝ) ^ (-(mb : Int))

/-- `unitRoundoff = machineEpsilon / 2`. -/
theorem unitRoundoff_eq_half_machineEpsilon :
    unitRoundoff eb mb = machineEpsilon eb mb / 2 := by
  unfold unitRoundoff machineEpsilon
  rw [show (-(mb : Int) - 1 : Int) = -(mb : Int) + (-1) from by ring]
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-! ## Relative bounds for normal rounded results -/

/-- An RNE result that is normal must have come from the in-range
    branch of the RNE spec. -/
theorem in_range_of_rne_normal
    (r : ℝ) (z : IEEEFloat eb mb)
    (h_rne : IsRoundedToNearestEven r z)
    (h_norm : z.isNormal = true) :
    |r| < overflowBoundary eb mb := by
  by_contra h_not
  have h_over : overflowBoundary eb mb ≤ |r| := le_of_not_gt h_not
  rcases le_or_gt 0 r with h_nonneg | h_neg
  · have hz : z = .inf false := (h_rne.1 h_over).1 h_nonneg
    subst hz
    simp [isNormal] at h_norm
  · have hz : z = .inf true := (h_rne.1 h_over).2 h_neg
    subst hz
    simp [isNormal] at h_norm

/-- For a normal finite encoding, its ULP is no larger than its
    magnitude. -/
theorem ulp_le_abs_of_normal {x : IEEEFloat eb mb}
    (h_norm : x.isNormal = true) :
    x.ulp ≤ |x.toRealOrZero| := by
  cases x with
  | nan => simp [isNormal] at h_norm
  | inf _ => simp [isNormal] at h_norm
  | finite s e m =>
    simp [isNormal] at h_norm
    simp only [ulp, toRealOrZero, finiteValue]
    rw [if_neg h_norm]
    simp only [h_norm, ↓reduceIte]
    rw [abs_mul, abs_mul]
    have h_sign_abs : |(if s then (-1 : ℝ) else 1)| = 1 := by
      cases s <;> simp
    rw [h_sign_abs, one_mul]
    have h_pow_pos : 0 < (2 : ℝ) ^ ((e.val : Int) - bias eb) :=
      zpow_pos (by norm_num) _
    have h_mant_pos : 0 < 1 + (m.val : ℝ) / (2 : ℝ) ^ mb := by positivity
    rw [abs_of_pos h_pow_pos, abs_of_pos h_mant_pos]
    have h_pow_mb_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ mb := by
      have h_nat : (1 : Nat) ≤ 2 ^ mb := Nat.one_le_two_pow
      exact_mod_cast h_nat
    rw [show ((e.val : Int) - bias eb - (mb : Int)) =
        ((e.val : Int) - bias eb) + (-(mb : Int)) by ring]
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_neg, zpow_natCast]
    have h_nonneg_pow : 0 ≤ (2 : ℝ) ^ ((e.val : Int) - bias eb) :=
      le_of_lt h_pow_pos
    have h_le_factor : ((2 : ℝ) ^ mb)⁻¹ ≤ 1 + (m.val : ℝ) / (2 : ℝ) ^ mb := by
      have h_inv_le_one : ((2 : ℝ) ^ mb)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ h_pow_mb_ge_one
      have h_nonneg_div : 0 ≤ (m.val : ℝ) / (2 : ℝ) ^ mb := by positivity
      linarith
    exact mul_le_mul_of_nonneg_left h_le_factor h_nonneg_pow

/-- For a normal finite encoding, `ulp x ≤ ε |x|`, where
    `ε = 2^{-mb}` is `machineEpsilon`. -/
theorem ulp_le_machineEpsilon_mul_abs_of_normal {x : IEEEFloat eb mb}
    (h_norm : x.isNormal = true) :
    x.ulp ≤ machineEpsilon eb mb * |x.toRealOrZero| := by
  cases x with
  | nan => simp [isNormal] at h_norm
  | inf _ => simp [isNormal] at h_norm
  | finite s e m =>
    simp [isNormal] at h_norm
    simp only [ulp, toRealOrZero, finiteValue, machineEpsilon]
    rw [if_neg h_norm]
    simp only [h_norm, ↓reduceIte]
    rw [abs_mul, abs_mul]
    have h_sign_abs : |(if s then (-1 : ℝ) else 1)| = 1 := by
      cases s <;> simp
    rw [h_sign_abs, one_mul]
    have h_pow_pos : 0 < (2 : ℝ) ^ ((e.val : Int) - bias eb) :=
      zpow_pos (by norm_num) _
    have h_mant_pos : 0 < 1 + (m.val : ℝ) / (2 : ℝ) ^ mb := by positivity
    rw [abs_of_pos h_pow_pos, abs_of_pos h_mant_pos]
    rw [show ((e.val : Int) - bias eb - (mb : Int)) =
        ((e.val : Int) - bias eb) + (-(mb : Int)) by ring]
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have h_nonneg_left : 0 ≤ (2 : ℝ) ^ (-(mb : Int)) :=
      le_of_lt (zpow_pos (by norm_num) _)
    have h_nonneg_pow : 0 ≤ (2 : ℝ) ^ ((e.val : Int) - bias eb) :=
      le_of_lt h_pow_pos
    have h_factor : (1 : ℝ) ≤ 1 + (m.val : ℝ) / (2 : ℝ) ^ mb := by
      have h_div_nonneg : 0 ≤ (m.val : ℝ) / (2 : ℝ) ^ mb := by positivity
      linarith
    nlinarith [mul_le_mul_of_nonneg_left h_factor h_nonneg_pow, h_nonneg_left]

/-- If `r` rounds to `z` and the absolute error is at most half
    `|z|`, then `|z| / 2 ≤ |r|`. -/
theorem abs_result_half_le_abs_exact
    (r z : ℝ)
    (h_err : |r - z| ≤ |z| / 2) :
    |z| / 2 ≤ |r| := by
  have h_triangle : |z| ≤ |r - z| + |r| := by
    calc
      |z| = |-(r - z) + r| := by ring_nf
      _ ≤ |-(r - z)| + |r| := abs_add_le (-(r - z)) r
      _ = |r - z| + |r| := by rw [abs_neg]
  linarith

/-- Normal RNE results satisfy the standard `1 ulp` relative-error
    bound with `machineEpsilon eb mb = 2^{-mb}`. -/
theorem rne_normal_relative_error
    (heb : 2 ≤ eb) (hmb : 1 ≤ mb)
    (r : ℝ) (z : IEEEFloat eb mb)
    (h_rne : IsRoundedToNearestEven r z)
    (h_norm : z.isNormal = true) :
    |r - z.toRealOrZero| ≤ machineEpsilon eb mb * |r| := by
  have hover := in_range_of_rne_normal (eb := eb) (mb := mb) r z h_rne h_norm
  have h_abs : |r - z.toRealOrZero| ≤ z.ulp / 2 :=
    half_ulp_bound heb hmb r z (IsRoundedToNearest.of_rne h_rne) hover
  have h_ulp_rel : z.ulp ≤ machineEpsilon eb mb * |z.toRealOrZero| :=
    ulp_le_machineEpsilon_mul_abs_of_normal (eb := eb) (mb := mb) h_norm
  have h_ulp_abs : z.ulp ≤ |z.toRealOrZero| :=
    ulp_le_abs_of_normal (eb := eb) (mb := mb) h_norm
  have h_abs_z : |r - z.toRealOrZero| ≤ |z.toRealOrZero| / 2 := by
    nlinarith
  have h_z_half : |z.toRealOrZero| / 2 ≤ |r| :=
    abs_result_half_le_abs_exact r z.toRealOrZero h_abs_z
  have h_eps_nonneg : 0 ≤ machineEpsilon eb mb := by
    unfold machineEpsilon
    positivity
  have h_ulp_half :
      z.ulp / 2 ≤ machineEpsilon eb mb * (|z.toRealOrZero| / 2) := by
    nlinarith
  have h_rel_target : z.ulp / 2 ≤ machineEpsilon eb mb * |r| := by
    exact le_trans h_ulp_half (mul_le_mul_of_nonneg_left h_z_half h_eps_nonneg)
  exact le_trans h_abs h_rel_target

/-! ## Relative bounds for backend operations with normal results -/

/-- Correctly-rounded addition satisfies the normal-result relative
    error bound. -/
theorem add_relative_error_normal
    (heb : 2 ≤ eb) (hmb : 1 ≤ mb)
    (x y : IEEEFloat eb mb)
    (h_norm : (add (le_trans (by decide) heb) hmb x y).isNormal = true) :
    |(add (le_trans (by decide) heb) hmb x y).toRealOrZero -
        (x.toRealOrZero + y.toRealOrZero)|
      ≤ machineEpsilon eb mb * |x.toRealOrZero + y.toRealOrZero| := by
  cases x with
  | nan => simp [add, isNormal] at h_norm
  | inf sx =>
    cases y with
    | nan => simp [add, isNormal] at h_norm
    | inf sy =>
      by_cases hsign : sx = sy <;> simp [add, hsign, isNormal] at h_norm
    | finite _ _ _ => simp [add, isNormal] at h_norm
  | finite sx ex mx =>
    cases y with
    | nan => simp [add, isNormal] at h_norm
    | inf _ => simp [add, isNormal] at h_norm
    | finite sy ey my =>
      simp only [add, toRealOrZero]
      rw [abs_sub_comm]
      exact rne_normal_relative_error heb hmb _ _
        (roundToNearestEven_isRNE (le_trans (by decide) heb) hmb _) h_norm

/-- Correctly-rounded subtraction satisfies the normal-result relative
    error bound. -/
theorem sub_relative_error_normal
    (heb : 2 ≤ eb) (hmb : 1 ≤ mb)
    (x y : IEEEFloat eb mb)
    (h_norm : (sub (le_trans (by decide) heb) hmb x y).isNormal = true) :
    |(sub (le_trans (by decide) heb) hmb x y).toRealOrZero -
        (x.toRealOrZero - y.toRealOrZero)|
      ≤ machineEpsilon eb mb * |x.toRealOrZero - y.toRealOrZero| := by
  cases x with
  | nan => simp [sub, isNormal] at h_norm
  | inf sx =>
    cases y with
    | nan => simp [sub, isNormal] at h_norm
    | inf sy =>
      by_cases hsign : sx = sy <;> simp [sub, hsign, isNormal] at h_norm
    | finite _ _ _ => simp [sub, isNormal] at h_norm
  | finite sx ex mx =>
    cases y with
    | nan => simp [sub, isNormal] at h_norm
    | inf _ => simp [sub, isNormal] at h_norm
    | finite sy ey my =>
      simp only [sub, toRealOrZero]
      rw [abs_sub_comm]
      exact rne_normal_relative_error heb hmb _ _
        (roundToNearestEven_isRNE (le_trans (by decide) heb) hmb _) h_norm

/-- Correctly-rounded multiplication satisfies the normal-result
    relative error bound. -/
theorem mul_relative_error_normal
    (heb : 2 ≤ eb) (hmb : 1 ≤ mb)
    (x y : IEEEFloat eb mb)
    (h_norm : (mul (le_trans (by decide) heb) hmb x y).isNormal = true) :
    |(mul (le_trans (by decide) heb) hmb x y).toRealOrZero -
        (x.toRealOrZero * y.toRealOrZero)|
      ≤ machineEpsilon eb mb * |x.toRealOrZero * y.toRealOrZero| := by
  cases x with
  | nan => simp [mul, isNormal] at h_norm
  | inf sx =>
    cases y with
    | nan => simp [mul, isNormal] at h_norm
    | inf _ => simp [mul, isNormal] at h_norm
    | finite sy ey my =>
      by_cases hyz : (IEEEFloat.finite sy ey my : IEEEFloat eb mb).isZero
      · simp [mul, hyz, isNormal] at h_norm
      · simp [mul, hyz, isNormal] at h_norm
  | finite sx ex mx =>
    cases y with
    | nan => simp [mul, isNormal] at h_norm
    | inf _ =>
      by_cases hxz : (IEEEFloat.finite sx ex mx : IEEEFloat eb mb).isZero
      · simp [mul, hxz, isNormal] at h_norm
      · simp [mul, hxz, isNormal] at h_norm
    | finite sy ey my =>
      simp only [mul, toRealOrZero]
      rw [abs_sub_comm]
      exact rne_normal_relative_error heb hmb _ _
        (roundToNearestEven_isRNE (le_trans (by decide) heb) hmb _) h_norm

/-- Correctly-rounded division satisfies the normal-result relative
    error bound. -/
theorem div_relative_error_normal
    (heb : 2 ≤ eb) (hmb : 1 ≤ mb)
    (x y : IEEEFloat eb mb)
    (h_norm : (div (le_trans (by decide) heb) hmb x y).isNormal = true) :
    |(div (le_trans (by decide) heb) hmb x y).toRealOrZero -
        (x.toRealOrZero / y.toRealOrZero)|
      ≤ machineEpsilon eb mb * |x.toRealOrZero / y.toRealOrZero| := by
  cases x with
  | nan => simp [div, isNormal] at h_norm
  | inf _ =>
    cases y with
    | nan => simp [div, isNormal] at h_norm
    | inf _ => simp [div, isNormal] at h_norm
    | finite _ _ _ => simp [div, isNormal] at h_norm
  | finite sx ex mx =>
    cases y with
    | nan => simp [div, isNormal] at h_norm
    | inf _ => simp [div, isNormal] at h_norm
    | finite sy ey my =>
      by_cases hyz : (IEEEFloat.finite sy ey my : IEEEFloat eb mb).isZero
      · by_cases hxz : (IEEEFloat.finite sx ex mx : IEEEFloat eb mb).isZero
        · simp [div, hyz, hxz, isNormal] at h_norm
        · simp [div, hyz, hxz, isNormal] at h_norm
      · have h_norm_rne :
            (roundToNearestEven (le_trans (by decide) heb) hmb
              (finiteValue sx ex mx / finiteValue sy ey my)).isNormal = true := by
          simpa [div, hyz] using h_norm
        simp only [div, toRealOrZero]
        rw [if_neg hyz]
        rw [abs_sub_comm]
        exact rne_normal_relative_error heb hmb _ _
          (roundToNearestEven_isRNE (le_trans (by decide) heb) hmb _) h_norm_rne

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
