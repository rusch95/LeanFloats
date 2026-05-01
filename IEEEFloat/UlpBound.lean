import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import IEEEFloat.RoundExistence

/-! # Half-ULP bound for round-to-nearest

The headline result of error analysis: for any in-range `r` and
finite RN witness `x`, `|r − x.toRealOrZero| ≤ x.ulp / 2`.

The standard "rounding error is at most half a unit in the last
place" bound underlies essentially all relative-error / Sterbenz
arguments downstream.

## Hypotheses

`half_ulp_bound` requires `2 ≤ eb` (so that the maximum-magnitude
finite encoding sits in the normal range, matching the `maxFinite`
formula) and `1 ≤ mb` (so that `±2^minSubnormalExp` is representable
for use as a comparator at the `±0` plateau).  All standard formats
(binary16/32/64, bfloat16) satisfy both. -/

namespace IEEEFloat

variable {eb mb : Nat}

/-- The encoding successor of a finite `x` is at most `ulp(x)` above
    `x` in real value (when finite).

    Within-stratum and `−0 → +0` cases proved.  Cross-stratum cases
    deferred (the explicit gap-vs-ulp algebra is in
    `IEEEFloat.Spacing` `*_cross_*_diff` lemmas, but routing through
    them with abstract `x` requires Fin-level encoding rewrites). -/
private theorem gap_up_le_ulp
    (x : IEEEFloat eb mb) (h_fin : x.isFinite = true)
    (h_succ_fin : (nextFinite x).isFinite = true) :
    (nextFinite x).toRealOrZero - x.toRealOrZero ≤ x.ulp := by
  have h_ulp_pos : 0 < x.ulp := ulp_pos_of_finite h_fin
  match x, h_fin with
  | .finite false e m, _ =>
      simp only [nextFinite] at h_succ_fin ⊢
      split
      · -- positive within: gap = ulp.
        rename_i h_m
        rw [toRealOrZero_finite_eq, toRealOrZero_finite_eq]
        have h := nextFinite_value_pos_within (eb := eb) (mb := mb) e m h_m
        linarith
      · split
        · -- positive cross: gap = ulp (sub→norm and norm→norm).
          rename_i h_m h_e
          push_neg at h_m
          have h_m_eq : m.val = 2 ^ mb - 1 := by have := m.isLt; omega
          have h_zero : 0 < 2 ^ mb := Nat.pow_pos (by decide)
          have h_max : 2 ^ mb - 1 < 2 ^ mb := by omega
          rw [toRealOrZero_finite_eq, toRealOrZero_finite_eq]
          by_cases h_e_zero : e.val = 0
          · -- positive cross subnormal: gap = 2^minSubExp = ulp (at e=0).
            have h_e_old : 0 < 2 ^ eb - 1 := h_e_zero ▸ e.isLt
            have h_e_new : 1 < 2 ^ eb - 1 := by omega
            have h_diff := finiteValue_pos_cross_subnormal_diff
              (eb := eb) (mb := mb) h_e_new h_e_old h_max h_zero
            have he_eq : e = (⟨0, h_e_old⟩ : Fin (2 ^ eb - 1)) := Fin.ext h_e_zero
            have hm_eq : m = (⟨2 ^ mb - 1, h_max⟩ : Fin (2 ^ mb)) := Fin.ext h_m_eq
            have h_ulp_eq : (.finite false e m : IEEEFloat eb mb).ulp
                          = (2 : ℝ) ^ minSubnormalExp eb mb := by
              rw [show (.finite false e m : IEEEFloat eb mb).ulp = (2 : ℝ) ^ minSubnormalExp eb mb
                  from by simp [ulp, h_e_zero]]
            rw [h_ulp_eq]
            subst hm_eq
            subst he_eq
            exact le_of_eq h_diff
          · -- positive cross normal: gap = 2^{e-bias-mb} = ulp (at e≥1).
            have h_e_pos : 1 ≤ e.val := Nat.one_le_iff_ne_zero.mpr h_e_zero
            have h_diff := finiteValue_pos_cross_normal_diff
              (eb := eb) (mb := mb) e.val h_e_pos e.isLt h_e h_max h_zero
            have hm_eq : m = (⟨2 ^ mb - 1, h_max⟩ : Fin (2 ^ mb)) := Fin.ext h_m_eq
            have h_ulp_eq : (.finite false e m : IEEEFloat eb mb).ulp
                          = (2 : ℝ) ^ ((e.val : Int) - bias eb - (mb : Int)) := by
              simp [ulp, h_e_zero]
            rw [h_ulp_eq]
            subst hm_eq
            exact le_of_eq h_diff
        · -- positive max → +∞: contradicts h_succ_fin.
          rename_i h_m h_e
          simp [h_m, h_e, isFinite] at h_succ_fin
  | .finite true e m, _ =>
      simp only [nextFinite] at h_succ_fin ⊢
      split
      · -- negative within (m -= 1): gap = ulp.
        rename_i h_m
        rw [toRealOrZero_finite_eq, toRealOrZero_finite_eq]
        have h_m_pos : 1 ≤ m.val := Nat.one_le_iff_ne_zero.mpr h_m
        have h_m1 : m.val - 1 + 1 < 2 ^ mb := by have := m.isLt; omega
        have h := finiteValue_neg_within_diff (eb := eb) (mb := mb) e
          ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) m.isLt⟩ h_m1
        have hm_cast : (⟨(m.val - 1) + 1, h_m1⟩ : Fin (2 ^ mb)) = m := by
          apply Fin.ext; show (m.val - 1) + 1 = m.val; omega
        rw [hm_cast] at h
        have h_ulp_eq : (.finite true e ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) m.isLt⟩
                          : IEEEFloat eb mb).ulp
                      = (.finite true e m : IEEEFloat eb mb).ulp := by
          simp [ulp]
        rw [h_ulp_eq] at h
        linarith
      · split
        · -- negative cross: gap = ulp (e=1) or ulp/2 (e≥2).
          rename_i h_m h_e
          push_neg at h_m
          have h_m_zero : m.val = 0 := h_m
          have h_zero : 0 < 2 ^ mb := Nat.pow_pos (by decide)
          have h_max : 2 ^ mb - 1 < 2 ^ mb := by have := m.isLt; omega
          rw [toRealOrZero_finite_eq, toRealOrZero_finite_eq]
          by_cases h_e_one : e.val = 1
          · -- negative cross to subnormal: gap = 2^minSubExp = ulp (at e=1).
            have h_e_old : (1 : Nat) < 2 ^ eb - 1 := by
              have := e.isLt; rw [h_e_one] at this; exact this
            have h_e_new : (0 : Nat) < 2 ^ eb - 1 := by omega
            have h_diff := finiteValue_neg_cross_to_subnormal_diff
              (eb := eb) (mb := mb) h_e_old h_e_new h_max h_zero
            have he_eq : e = (⟨1, h_e_old⟩ : Fin (2 ^ eb - 1)) := Fin.ext h_e_one
            have hm_eq : m = (⟨0, h_zero⟩ : Fin (2 ^ mb)) := Fin.ext h_m_zero
            have h_ulp_eq : (.finite true e m : IEEEFloat eb mb).ulp
                          = (2 : ℝ) ^ minSubnormalExp eb mb := by
              simp [ulp, h_e_one, h_e, minSubnormalExp, minNormalExp]
            rw [h_ulp_eq]
            subst hm_eq
            subst he_eq
            exact le_of_eq h_diff
          · -- negative cross to normal: gap = 2^{e-1-bias-mb} = ulp/2 < ulp.
            have h_e_ge_2 : 2 ≤ e.val := by
              have h_e_ne : e.val ≠ 0 := h_e
              omega
            have h_e_pred_lt : e.val - 1 < 2 ^ eb - 1 :=
              lt_of_le_of_lt (Nat.sub_le _ _) e.isLt
            have h_diff := finiteValue_neg_cross_to_normal_diff
              (eb := eb) (mb := mb) e.val h_e_ge_2 e.isLt h_e_pred_lt h_max h_zero
            have hm_eq : m = (⟨0, h_zero⟩ : Fin (2 ^ mb)) := Fin.ext h_m_zero
            have h_ulp_eq : (.finite true e m : IEEEFloat eb mb).ulp
                          = (2 : ℝ) ^ ((e.val : Int) - bias eb - (mb : Int)) := by
              simp [ulp, h_e]
            rw [h_ulp_eq]
            -- gap = 2^{e-1-bias-mb} ≤ 2^{e-bias-mb}
            have h_two_pow_le :
                (2 : ℝ) ^ ((e.val : Int) - 1 - bias eb - (mb : Int))
                  ≤ (2 : ℝ) ^ ((e.val : Int) - bias eb - (mb : Int)) := by
              apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
              omega
            subst hm_eq
            linarith [h_diff, h_two_pow_le]
        · -- −0 → +0: gap = 0.
          rename_i h_m h_e
          have ⟨h1, h2⟩ := nextFinite_value_eq_neg_zero e m h_m h_e
          rw [h1, h2]
          linarith

/-- Dual of `gap_up_le_ulp` for the encoding predecessor. -/
private theorem gap_down_le_ulp
    (x : IEEEFloat eb mb) (h_fin : x.isFinite = true)
    (h_pred_fin : (prevFinite x).isFinite = true) :
    x.toRealOrZero - (prevFinite x).toRealOrZero ≤ x.ulp := by
  have h_ulp_pos : 0 < x.ulp := ulp_pos_of_finite h_fin
  match x, h_fin with
  | .finite true e m, _ =>
      -- Negative going more negative.  Mirror of positive nextFinite.
      simp only [prevFinite] at h_pred_fin ⊢
      split
      · -- negative within: prev has m+1.  Gap = ulp.
        rename_i h_m
        rw [toRealOrZero_finite_eq, toRealOrZero_finite_eq]
        have h := finiteValue_neg_within_diff (eb := eb) (mb := mb) e m h_m
        linarith
      · split
        · -- negative cross down: gap = ulp.  Two subcases on e.
          rename_i h_m h_e
          push_neg at h_m
          have h_m_eq : m.val = 2 ^ mb - 1 := by have := m.isLt; omega
          have h_zero : 0 < 2 ^ mb := Nat.pow_pos (by decide)
          have h_max : 2 ^ mb - 1 < 2 ^ mb := by omega
          rw [toRealOrZero_finite_eq, toRealOrZero_finite_eq]
          by_cases h_e_zero : e.val = 0
          · -- subnormal x crossing to (true, 1, 0).  Gap = 2^minSubExp = ulp(e=0).
            have h_e_old : (1 : Nat) < 2 ^ eb - 1 := by
              have := h_e_zero ▸ h_e
              omega
            have h_e_new : (0 : Nat) < 2 ^ eb - 1 := h_e_zero ▸ e.isLt
            have h_diff := finiteValue_neg_cross_to_subnormal_diff
              (eb := eb) (mb := mb) h_e_old h_e_new h_max h_zero
            have he_eq : e = (⟨0, h_e_new⟩ : Fin (2 ^ eb - 1)) := Fin.ext h_e_zero
            have hm_eq : m = (⟨2 ^ mb - 1, h_max⟩ : Fin (2 ^ mb)) := Fin.ext h_m_eq
            have h_ulp_eq : (.finite true e m : IEEEFloat eb mb).ulp
                          = (2 : ℝ) ^ minSubnormalExp eb mb := by
              simp [ulp, h_e_zero]
            rw [h_ulp_eq]
            subst hm_eq
            subst he_eq
            exact le_of_eq h_diff
          · -- normal x (e ≥ 1) crossing to (true, e+1, 0).  Gap = ulp.
            have h_e_pos : 1 ≤ e.val := Nat.one_le_iff_ne_zero.mpr h_e_zero
            have h_e_old_lt : e.val + 1 < 2 ^ eb - 1 := h_e
            have h_e_new_lt : (e.val + 1) - 1 < 2 ^ eb - 1 := by
              have : e.val < 2 ^ eb - 1 := e.isLt
              omega
            have h_e_old_ge : 2 ≤ e.val + 1 := by omega
            have h_diff := finiteValue_neg_cross_to_normal_diff
              (eb := eb) (mb := mb) (e.val + 1) h_e_old_ge h_e_old_lt h_e_new_lt h_max h_zero
            have hm_eq : m = (⟨2 ^ mb - 1, h_max⟩ : Fin (2 ^ mb)) := Fin.ext h_m_eq
            have h_eq_e : (e.val + 1) - 1 = e.val := by omega
            have he_eq : (⟨(e.val + 1) - 1, h_e_new_lt⟩ : Fin (2 ^ eb - 1)) = e :=
              Fin.ext h_eq_e
            -- Rewrite h_diff to use e directly.
            rw [he_eq] at h_diff
            -- Normalise the exponent: ((e.val + 1 : Nat) : Int) - 1 = (e.val : Int).
            rw [show ((((e.val + 1 : Nat) : Int) - 1 - bias eb - (mb : Int)))
                  = ((e.val : Int) - bias eb - (mb : Int)) from by push_cast; ring] at h_diff
            have h_ulp_eq : (.finite true e m : IEEEFloat eb mb).ulp
                          = (2 : ℝ) ^ ((e.val : Int) - bias eb - (mb : Int)) := by
              simp [ulp, h_e_zero]
            rw [h_ulp_eq]
            subst hm_eq
            exact le_of_eq h_diff
        · -- negative max → -∞: contradicts h_pred_fin.
          rename_i h_m h_e
          simp [h_m, h_e, isFinite] at h_pred_fin
  | .finite false e m, _ =>
      simp only [prevFinite] at h_pred_fin ⊢
      split
      · -- positive within (m → m-1).  Gap = ulp.
        rename_i h_m
        rw [toRealOrZero_finite_eq, toRealOrZero_finite_eq]
        have h_m_pos : 1 ≤ m.val := Nat.one_le_iff_ne_zero.mpr h_m
        have h_m1 : m.val - 1 + 1 < 2 ^ mb := by have := m.isLt; omega
        have h := nextFinite_value_pos_within (eb := eb) (mb := mb) e
          ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) m.isLt⟩ h_m1
        have hm_cast : (⟨(m.val - 1) + 1, h_m1⟩ : Fin (2 ^ mb)) = m := by
          apply Fin.ext; show (m.val - 1) + 1 = m.val; omega
        rw [hm_cast] at h
        have h_ulp_eq : (.finite false e ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) m.isLt⟩
                          : IEEEFloat eb mb).ulp
                      = (.finite false e m : IEEEFloat eb mb).ulp := by
          simp [ulp]
        rw [h_ulp_eq] at h
        linarith
      · split
        · -- positive cross down: gap = ulp (e=1) or ulp/2 (e≥2).
          rename_i h_m h_e
          push_neg at h_m
          have h_m_zero : m.val = 0 := h_m
          have h_zero : 0 < 2 ^ mb := Nat.pow_pos (by decide)
          have h_max : 2 ^ mb - 1 < 2 ^ mb := by have := m.isLt; omega
          rw [toRealOrZero_finite_eq, toRealOrZero_finite_eq]
          by_cases h_e_one : e.val = 1
          · -- e = 1: prev is (false, 0, 2^mb-1).  Gap = 2^minSubExp = ulp(e=1).
            have h_e_old : (1 : Nat) < 2 ^ eb - 1 := by
              have := e.isLt; rw [h_e_one] at this; exact this
            have h_e_new : (0 : Nat) < 2 ^ eb - 1 := by omega
            have h_diff := finiteValue_pos_cross_subnormal_diff
              (eb := eb) (mb := mb) h_e_old h_e_new h_max h_zero
            have he_eq : e = (⟨1, h_e_old⟩ : Fin (2 ^ eb - 1)) := Fin.ext h_e_one
            have hm_eq : m = (⟨0, h_zero⟩ : Fin (2 ^ mb)) := Fin.ext h_m_zero
            have h_ulp_eq : (.finite false e m : IEEEFloat eb mb).ulp
                          = (2 : ℝ) ^ minSubnormalExp eb mb := by
              simp [ulp, h_e_one, h_e, minSubnormalExp, minNormalExp]
            rw [h_ulp_eq]
            subst hm_eq
            subst he_eq
            exact le_of_eq h_diff
          · -- e ≥ 2: prev is (false, e-1, 2^mb-1).  Gap = 2^{e-1-bias-mb} = ulp/2.
            have h_e_ge_2 : 2 ≤ e.val := by
              have h_e_ne : e.val ≠ 0 := h_e
              omega
            have h_e_pred_lt : e.val - 1 < 2 ^ eb - 1 :=
              lt_of_le_of_lt (Nat.sub_le _ _) e.isLt
            -- Use finiteValue_pos_cross_normal_diff with e_old = e.val - 1.
            have h_e_old_pos : 1 ≤ e.val - 1 := by omega
            have h_e_old_lt' : e.val - 1 < 2 ^ eb - 1 := h_e_pred_lt
            have h_e_new' : (e.val - 1) + 1 < 2 ^ eb - 1 := by
              have : e.val < 2 ^ eb - 1 := e.isLt
              have : (e.val - 1) + 1 = e.val := by omega
              omega
            have h_diff := finiteValue_pos_cross_normal_diff
              (eb := eb) (mb := mb) (e.val - 1) h_e_old_pos h_e_old_lt' h_e_new' h_max h_zero
            have hm_eq : m = (⟨0, h_zero⟩ : Fin (2 ^ mb)) := Fin.ext h_m_zero
            have h_eq_e : (e.val - 1) + 1 = e.val := by omega
            have he_eq : (⟨(e.val - 1) + 1, h_e_new'⟩ : Fin (2 ^ eb - 1)) = e := by
              apply Fin.ext; exact h_eq_e
            have h_ulp_eq : (.finite false e m : IEEEFloat eb mb).ulp
                          = (2 : ℝ) ^ ((e.val : Int) - bias eb - (mb : Int)) := by
              simp [ulp, h_e]
            rw [h_ulp_eq]
            -- Rewrite h_diff to use e directly.
            rw [he_eq] at h_diff
            -- gap = 2^{(e-1)-bias-mb} ≤ 2^{e-bias-mb} = ulp.
            have h_two_pow_le :
                (2 : ℝ) ^ (((e.val - 1 : Nat) : Int) - bias eb - (mb : Int))
                  ≤ (2 : ℝ) ^ ((e.val : Int) - bias eb - (mb : Int)) := by
              apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
              have h1 : 1 ≤ e.val := by omega
              push_cast [Nat.cast_sub h1]
              omega
            subst hm_eq
            linarith [h_diff, h_two_pow_le]
        · -- +0 → -0 plateau: gap = 0.
          rename_i h_m h_e
          push_neg at h_m h_e
          -- (.finite true e m).toRealOrZero = (.finite false e m).toRealOrZero = 0
          have ⟨h1, h2⟩ := nextFinite_value_eq_neg_zero (eb := eb) (mb := mb) e m
            (by simp [h_m]) (by simp [h_e])
          rw [h1, h2]
          linarith

/-! ## Half-ULP bound

Main theorem.  Within-stratum specialisations could pin down the
bound to `ulp(x)/2` exactly (instead of `≤`) modulo the asymmetric
power-of-two case; we don't pursue that refinement here. -/

/-- For any RN witness `x` of `r` and `x` finite (with `nextFinite x`
    finite, `nextFinite x` strictly above `x` in real value), the
    half-ulp bound on the upper side. -/
private theorem half_ulp_bound_above
    (r : ℝ) (x : IEEEFloat eb mb) (hx_fin : x.isFinite = true)
    (h_succ_fin : (nextFinite x).isFinite = true)
    (h_succ_strict : x.toRealOrZero < (nextFinite x).toRealOrZero)
    (hx_min : ∀ y : IEEEFloat eb mb, y.isFinite = true →
      |x.toRealOrZero - r| ≤ |y.toRealOrZero - r|)
    (h_gt : x.toRealOrZero < r) :
    r - x.toRealOrZero ≤ x.ulp / 2 := by
  by_contra h_contra
  push_neg at h_contra
  -- gap_up > 0 (h_succ_strict) and ≤ ulp.
  have h_gap_le := gap_up_le_ulp x hx_fin h_succ_fin
  -- |nextFinite x - r| < |x - r|.
  have h_y_closer : |(nextFinite x).toRealOrZero - r| < |x.toRealOrZero - r| := by
    have h_x_abs : |x.toRealOrZero - r| = r - x.toRealOrZero := by
      rw [abs_sub_comm]; exact abs_of_pos (sub_pos.mpr h_gt)
    by_cases h_y_le : (nextFinite x).toRealOrZero ≤ r
    · have h_y_abs : |(nextFinite x).toRealOrZero - r| = r - (nextFinite x).toRealOrZero := by
        rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.mpr h_y_le)
      rw [h_x_abs, h_y_abs]
      linarith
    · push_neg at h_y_le
      have h_y_abs : |(nextFinite x).toRealOrZero - r| = (nextFinite x).toRealOrZero - r :=
        abs_of_pos (sub_pos.mpr h_y_le)
      rw [h_x_abs, h_y_abs]
      linarith
  exact absurd (hx_min _ h_succ_fin) (not_le.mpr h_y_closer)

/-- Symmetric helper for the lower side. -/
private theorem half_ulp_bound_below
    (r : ℝ) (x : IEEEFloat eb mb) (hx_fin : x.isFinite = true)
    (h_pred_fin : (prevFinite x).isFinite = true)
    (h_pred_strict : (prevFinite x).toRealOrZero < x.toRealOrZero)
    (hx_min : ∀ y : IEEEFloat eb mb, y.isFinite = true →
      |x.toRealOrZero - r| ≤ |y.toRealOrZero - r|)
    (h_lt : r < x.toRealOrZero) :
    x.toRealOrZero - r ≤ x.ulp / 2 := by
  by_contra h_contra
  push_neg at h_contra
  have h_gap_le := gap_down_le_ulp x hx_fin h_pred_fin
  have h_y_closer : |(prevFinite x).toRealOrZero - r| < |x.toRealOrZero - r| := by
    have h_x_abs : |x.toRealOrZero - r| = x.toRealOrZero - r :=
      abs_of_pos (sub_pos.mpr h_lt)
    by_cases h_y_ge : r ≤ (prevFinite x).toRealOrZero
    · have h_y_abs : |(prevFinite x).toRealOrZero - r| = (prevFinite x).toRealOrZero - r :=
        abs_of_nonneg (sub_nonneg.mpr h_y_ge)
      rw [h_x_abs, h_y_abs]
      linarith
    · push_neg at h_y_ge
      have h_y_abs : |(prevFinite x).toRealOrZero - r| = r - (prevFinite x).toRealOrZero := by
        rw [abs_sub_comm]; exact abs_of_pos (sub_pos.mpr h_y_ge)
      rw [h_x_abs, h_y_abs]
      linarith
  exact absurd (hx_min _ h_pred_fin) (not_le.mpr h_y_closer)

/-- For any in-range `r` and finite RN witness `x`,
    `|r − x.toRealOrZero| ≤ x.ulp / 2`.

    Requires `1 ≤ mb` so that `±2^minSubnormalExp` is representable
    (used as a comparator in the `±0` plateau cases) and `2 ≤ eb`
    so that the maximum-magnitude finite encoding is normal (matching
    the `maxFinite` formula).  Every standard format (binary16/32/64,
    bfloat16) satisfies both. -/
theorem half_ulp_bound (heb : 2 ≤ eb) (hmb : 1 ≤ mb)
    (r : ℝ) (x : IEEEFloat eb mb)
    (hx_RN : IsRoundedToNearest r x)
    (hover : |r| < overflowBoundary eb mb) :
    |r - x.toRealOrZero| ≤ x.ulp / 2 := by
  obtain ⟨hx_fin, hx_min⟩ := hx_RN.2 hover
  have h_ulp_pos : 0 < x.ulp := ulp_pos_of_finite hx_fin
  rcases lt_trichotomy r x.toRealOrZero with h_lt | h_eq | h_gt
  · -- r < x.value
    have h_abs : |r - x.toRealOrZero| = x.toRealOrZero - r := by
      rw [abs_sub_comm]; exact abs_of_pos (sub_pos.mpr h_lt)
    rw [h_abs]
    -- Use half_ulp_bound_below with prevFinite as the comparator.
    -- Need: prevFinite x finite AND strictly below x.
    -- Cases on x:
    --   x = max_neg: r < x.value - ulp/2 = -overflowBoundary, contradicts hover.
    --   x = +0: prevFinite +0 = -0 (same value).  Use -smallest_sub manually.
    --   else: prevFinite x finite AND strictly less than x.
    cases x with
    | nan => simp [isFinite] at hx_fin
    | inf _ => simp [isFinite] at hx_fin
    | finite s e m =>
      by_cases h_max_neg : s = true ∧ e.val = 2 ^ eb - 2 ∧ m.val = 2 ^ mb - 1
      · -- max_neg: r < x.value - ulp/2 = -overflowBoundary, contradicts hover.
        obtain ⟨hs, he, hm⟩ := h_max_neg
        have h_2eb : (2 : Nat) ^ 2 ≤ 2 ^ eb := Nat.pow_le_pow_right (by decide) heb
        have h_e_ne : e.val ≠ 0 := by rw [he]; omega
        have h_e_int : (e.val : Int) = (2 : Int) ^ eb - 2 := by
          rw [show (e.val : Int) = ((e.val : Nat) : Int) from rfl, he,
              Nat.cast_sub (by omega : (2 : Nat) ≤ 2 ^ eb)]
          push_cast; rfl
        have h_e_minus_bias : (e.val : Int) - bias eb = maxExp eb := by
          rw [h_e_int]
          unfold maxExp bias
          have h_split : (2 : Int) ^ eb = 2 * (2 : Int) ^ (eb - 1) := by
            calc (2 : Int) ^ eb
                = (2 : Int) ^ ((eb - 1) + 1) := by
                  rw [Nat.sub_add_cancel (by omega : 1 ≤ eb)]
              _ = (2 : Int) ^ (eb - 1) * 2 := pow_succ _ _
              _ = 2 * (2 : Int) ^ (eb - 1) := by ring
          rw [h_split]; ring
        have h_x_val : (.finite s e m : IEEEFloat eb mb).toRealOrZero = -maxFinite eb mb := by
          rw [hs, toRealOrZero_finite_eq]
          unfold finiteValue maxFinite
          rw [if_neg h_e_ne]
          simp only [if_true]
          rw [show (m.val : ℝ) = (2 : ℝ) ^ mb - 1 by
              rw [show (m.val : ℝ) = ((m.val : Nat) : ℝ) from rfl, hm,
                  cast_two_pow_sub_one]]
          rw [h_e_minus_bias, zpow_neg, zpow_natCast]
          field_simp
          ring
        have h_x_ulp : (.finite s e m : IEEEFloat eb mb).ulp = topUlp eb mb := by
          show (if e.val = 0 then (2 : ℝ) ^ minSubnormalExp eb mb
                else (2 : ℝ) ^ ((e.val : Int) - bias eb - (mb : Int))) = topUlp eb mb
          rw [if_neg h_e_ne]
          rw [show (e.val : Int) - bias eb - (mb : Int) = maxExp eb - (mb : Int) by
              rw [h_e_minus_bias]]
          rfl
        rw [h_x_val, h_x_ulp]
        -- maxFinite > 0 ⇒ x.value = -maxFinite < 0, r < x.value ⇒ r < 0, |r| = -r.
        have h_max_finite_pos : 0 < maxFinite eb mb := by
          unfold maxFinite
          have h_mb_pow_ge : (1 : ℝ) ≤ (2 : ℝ) ^ mb := one_le_pow₀ (by norm_num)
          have h_neg_le_one : (2 : ℝ) ^ (-(mb : Int)) ≤ 1 := by
            rw [zpow_neg, zpow_natCast]
            exact inv_le_one_of_one_le₀ h_mb_pow_ge
          have h_factor_pos : (0 : ℝ) < 2 - (2 : ℝ) ^ (-(mb : Int)) := by linarith
          have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ maxExp eb := zpow_pos (by norm_num) _
          exact mul_pos h_factor_pos h_pow_pos
        have h_r_neg : r ≤ 0 := by
          rw [h_x_val] at h_lt
          linarith
        have h_r_abs : |r| = -r := abs_of_nonpos h_r_neg
        rw [h_r_abs] at hover
        -- hover : -r < overflowBoundary = maxFinite + topUlp/2.
        unfold overflowBoundary at hover
        linarith
      · by_cases h_pos_zero : s = false ∧ e.val = 0 ∧ m.val = 0
        · -- x = +0: prevFinite (+0) = -0 (same value).  Use -smallest_sub directly.
          obtain ⟨hs, he, hm⟩ := h_pos_zero
          have h_e_pos : 0 < 2 ^ eb - 1 := by
            have := e.isLt; rw [he] at this; exact this
          have h_m_two : 1 < 2 ^ mb := by
            have h2 : 2 ^ 1 ≤ 2 ^ mb := Nat.pow_le_pow_right (by decide) hmb
            omega
          have h_zero_lt_mb : 0 < 2 ^ mb := Nat.pow_pos (by decide)
          let y : IEEEFloat eb mb := .finite true ⟨0, h_e_pos⟩ ⟨1, h_m_two⟩
          have hy_fin : y.isFinite = true := rfl
          have hy_val : y.toRealOrZero = -(2 : ℝ) ^ minSubnormalExp eb mb := by
            show finiteValue true (⟨0, h_e_pos⟩ : Fin (2 ^ eb - 1))
                                  (⟨1, h_m_two⟩ : Fin (2 ^ mb))
              = -(2 : ℝ) ^ minSubnormalExp eb mb
            simp only [finiteValue, ↓reduceIte]
            rw [show minSubnormalExp eb mb = minNormalExp eb - (mb : Int) from rfl,
                zpow_sub_natCast]
            push_cast; ring
          have hx_val : (.finite s e m : IEEEFloat eb mb).toRealOrZero = 0 := by
            rw [hs, toRealOrZero_finite_eq]
            have he_cast : e = (⟨0, h_e_pos⟩ : Fin (2 ^ eb - 1)) := Fin.ext he
            have hm_cast : m = (⟨0, h_zero_lt_mb⟩ : Fin (2 ^ mb)) := Fin.ext hm
            rw [he_cast, hm_cast]
            exact finiteValue_zero_pos h_e_pos h_zero_lt_mb
          have hx_ulp : (.finite s e m : IEEEFloat eb mb).ulp
                      = (2 : ℝ) ^ minSubnormalExp eb mb := by
            simp [ulp, he]
          have hxy := hx_min y hy_fin
          rw [hx_val, hy_val] at hxy
          have h_r_neg : r < 0 := by rw [← hx_val]; exact h_lt
          have h_x_abs : |(0 : ℝ) - r| = -r := by
            rw [zero_sub, abs_neg, abs_of_neg h_r_neg]
          rw [h_x_abs] at hxy
          have h_2pow_pos : (0 : ℝ) < (2 : ℝ) ^ minSubnormalExp eb mb :=
            zpow_pos (by norm_num) _
          rw [hx_val, hx_ulp]
          by_cases h_r_ge : -((2 : ℝ) ^ minSubnormalExp eb mb) ≤ r
          · have h_y_abs : |(-(2 : ℝ) ^ minSubnormalExp eb mb) - r|
                         = r + (2 : ℝ) ^ minSubnormalExp eb mb := by
              rw [show (-(2 : ℝ) ^ minSubnormalExp eb mb) - r
                    = -(r + (2 : ℝ) ^ minSubnormalExp eb mb) from by ring]
              rw [abs_neg, abs_of_nonneg]
              linarith
            rw [h_y_abs] at hxy
            linarith
          · push_neg at h_r_ge
            exfalso
            have h_y_abs : |(-(2 : ℝ) ^ minSubnormalExp eb mb) - r|
                         = (-(2 : ℝ) ^ minSubnormalExp eb mb) - r := by
              apply abs_of_nonneg; linarith
            rw [h_y_abs] at hxy
            linarith
        · -- Generic: use prevFinite x.
          have h_pred_fin : (prevFinite (.finite s e m : IEEEFloat eb mb)).isFinite = true := by
            cases s with
            | true =>
              simp only [prevFinite]
              by_cases h1 : m.val + 1 < 2 ^ mb
              · simp [h1, isFinite]
              · by_cases h2 : e.val + 1 < 2 ^ eb - 1
                · simp [h1, h2, isFinite]
                · exfalso
                  push_neg at h1 h2
                  apply h_max_neg
                  refine ⟨rfl, ?_, ?_⟩
                  · have := e.isLt; omega
                  · have := m.isLt; omega
            | false =>
              simp only [prevFinite]
              by_cases h1 : m.val ≠ 0
              · simp [h1, isFinite]
              · by_cases h2 : e.val ≠ 0
                · simp [h1, h2, isFinite]
                · simp [h1, h2, isFinite]
          have h_pred_strict : (prevFinite (.finite s e m : IEEEFloat eb mb)).toRealOrZero
                              < (.finite s e m : IEEEFloat eb mb).toRealOrZero := by
            cases s with
            | true =>
              simp only [prevFinite]
              by_cases h1 : m.val + 1 < 2 ^ mb
              · simp only [dif_pos h1]
                rw [toRealOrZero_finite_eq, toRealOrZero_finite_eq]
                have h := finiteValue_neg_within_diff (eb := eb) (mb := mb) e m h1
                have h_ulp_pos' : 0 <
                    (IEEEFloat.finite true e ⟨m.val + 1, h1⟩ : IEEEFloat eb mb).ulp := by
                  apply ulp_pos_of_finite; rfl
                linarith
              · by_cases h2 : e.val + 1 < 2 ^ eb - 1
                · simp only [dif_neg h1, dif_pos h2]
                  push_neg at h1
                  have h_m_eq : m.val = 2 ^ mb - 1 := by have := m.isLt; omega
                  have h_zero : 0 < 2 ^ mb := Nat.pow_pos (by decide)
                  have h_max : 2 ^ mb - 1 < 2 ^ mb := by omega
                  rw [toRealOrZero_finite_eq, toRealOrZero_finite_eq]
                  -- value diff > 0; gap_down > 0 always for negative non-±0.
                  -- (true, e+1, 0).value < (true, e, 2^mb-1).value
                  by_cases h_e_zero : e.val = 0
                  · -- subnormal x; prev = (true, 1, 0).
                    have h_e_old : (1 : Nat) < 2 ^ eb - 1 := by
                      have := h_e_zero ▸ h2; omega
                    have h_e_new : (0 : Nat) < 2 ^ eb - 1 := h_e_zero ▸ e.isLt
                    have h_diff := finiteValue_neg_cross_to_subnormal_diff
                      (eb := eb) (mb := mb) h_e_old h_e_new h_max h_zero
                    have he_eq : e = (⟨0, h_e_new⟩ : Fin (2 ^ eb - 1)) := Fin.ext h_e_zero
                    have hm_eq : m = (⟨2 ^ mb - 1, h_max⟩ : Fin (2 ^ mb)) := Fin.ext h_m_eq
                    subst hm_eq
                    subst he_eq
                    have h_pos : (0 : ℝ) < (2 : ℝ) ^ minSubnormalExp eb mb :=
                      zpow_pos (by norm_num) _
                    show finiteValue (eb := eb) (mb := mb) true ⟨1, h_e_old⟩ ⟨0, h_zero⟩
                       < finiteValue true ⟨0, h_e_new⟩ ⟨2 ^ mb - 1, h_max⟩
                    linarith
                  · have h_e_pos : 1 ≤ e.val := Nat.one_le_iff_ne_zero.mpr h_e_zero
                    have h_e_old_lt : e.val + 1 < 2 ^ eb - 1 := h2
                    have h_e_new_lt : (e.val + 1) - 1 < 2 ^ eb - 1 := by
                      have := e.isLt; omega
                    have h_e_old_ge : 2 ≤ e.val + 1 := by omega
                    have h_diff := finiteValue_neg_cross_to_normal_diff
                      (eb := eb) (mb := mb) (e.val + 1) h_e_old_ge h_e_old_lt h_e_new_lt h_max h_zero
                    have h_eq_e : (e.val + 1) - 1 = e.val := by omega
                    have he_eq : (⟨(e.val + 1) - 1, h_e_new_lt⟩ : Fin (2 ^ eb - 1)) = e :=
                      Fin.ext h_eq_e
                    rw [he_eq] at h_diff
                    have hm_eq : m = (⟨2 ^ mb - 1, h_max⟩ : Fin (2 ^ mb)) := Fin.ext h_m_eq
                    subst hm_eq
                    have h_two_pow_pos : (0 : ℝ) <
                        (2 : ℝ) ^ (((e.val + 1 : Nat) : Int) - 1 - bias eb - (mb : Int)) :=
                      zpow_pos (by norm_num) _
                    linarith
                · exfalso
                  push_neg at h2
                  apply h_max_neg
                  have h_m_eq : m.val = 2 ^ mb - 1 := by
                    push_neg at h1; have := m.isLt; omega
                  refine ⟨rfl, ?_, h_m_eq⟩
                  have := e.isLt; omega
            | false =>
              -- positive: prev goes down toward zero.
              simp only [prevFinite]
              by_cases h1 : m.val ≠ 0
              · simp only [dif_pos h1]
                rw [toRealOrZero_finite_eq, toRealOrZero_finite_eq]
                have h_m_pos : 1 ≤ m.val := Nat.one_le_iff_ne_zero.mpr h1
                have h_m1 : m.val - 1 + 1 < 2 ^ mb := by have := m.isLt; omega
                have h := nextFinite_value_pos_within (eb := eb) (mb := mb) e
                  ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) m.isLt⟩ h_m1
                have hm_cast : (⟨(m.val - 1) + 1, h_m1⟩ : Fin (2 ^ mb)) = m := by
                  apply Fin.ext; show (m.val - 1) + 1 = m.val; omega
                rw [hm_cast] at h
                have h_ulp_pos' : 0 <
                    (.finite false e ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) m.isLt⟩
                      : IEEEFloat eb mb).ulp := ulp_pos_of_finite rfl
                linarith
              · by_cases h2 : e.val ≠ 0
                · simp only [dif_neg h1, dif_pos h2]
                  push_neg at h1
                  have h_m_zero : m.val = 0 := h1
                  have h_zero : 0 < 2 ^ mb := Nat.pow_pos (by decide)
                  have h_max : 2 ^ mb - 1 < 2 ^ mb := by have := m.isLt; omega
                  rw [toRealOrZero_finite_eq, toRealOrZero_finite_eq]
                  by_cases h_e_one : e.val = 1
                  · have h_e_old : (1 : Nat) < 2 ^ eb - 1 := by
                      have := e.isLt; rw [h_e_one] at this; exact this
                    have h_e_new : (0 : Nat) < 2 ^ eb - 1 := by omega
                    have h_diff := finiteValue_pos_cross_subnormal_diff
                      (eb := eb) (mb := mb) h_e_old h_e_new h_max h_zero
                    have he_eq : e = (⟨1, h_e_old⟩ : Fin (2 ^ eb - 1)) := Fin.ext h_e_one
                    have hm_eq : m = (⟨0, h_zero⟩ : Fin (2 ^ mb)) := Fin.ext h_m_zero
                    subst hm_eq
                    subst he_eq
                    have h_pos : (0 : ℝ) < (2 : ℝ) ^ minSubnormalExp eb mb :=
                      zpow_pos (by norm_num) _
                    show finiteValue (eb := eb) (mb := mb) false ⟨0, h_e_new⟩ ⟨2 ^ mb - 1, h_max⟩
                       < finiteValue false ⟨1, h_e_old⟩ ⟨0, h_zero⟩
                    linarith
                  · have h_e_ge_2 : 2 ≤ e.val := by
                      have h_e_ne : e.val ≠ 0 := h2
                      omega
                    have h_e_pred_lt : e.val - 1 < 2 ^ eb - 1 :=
                      lt_of_le_of_lt (Nat.sub_le _ _) e.isLt
                    have h_e_old_pos : 1 ≤ e.val - 1 := by omega
                    have h_e_new' : (e.val - 1) + 1 < 2 ^ eb - 1 := by
                      have h1 : 1 ≤ e.val := by omega
                      have h2 : e.val < 2 ^ eb - 1 := e.isLt
                      have h3 : (e.val - 1) + 1 = e.val := by omega
                      omega
                    have h_diff := finiteValue_pos_cross_normal_diff
                      (eb := eb) (mb := mb) (e.val - 1) h_e_old_pos h_e_pred_lt h_e_new' h_max h_zero
                    have h_eq_e : (e.val - 1) + 1 = e.val := by omega
                    have he_eq : (⟨(e.val - 1) + 1, h_e_new'⟩ : Fin (2 ^ eb - 1)) = e :=
                      Fin.ext h_eq_e
                    rw [he_eq] at h_diff
                    have hm_eq : m = (⟨0, h_zero⟩ : Fin (2 ^ mb)) := Fin.ext h_m_zero
                    subst hm_eq
                    have h_two_pow_pos : (0 : ℝ) <
                        (2 : ℝ) ^ (((e.val - 1 : Nat) : Int) - bias eb - (mb : Int)) :=
                      zpow_pos (by norm_num) _
                    linarith
                · -- e = 0, m = 0: x = +0.  Contradicts h_pos_zero.
                  push_neg at h1 h2
                  exfalso
                  apply h_pos_zero
                  refine ⟨rfl, h2, h1⟩
          exact half_ulp_bound_below r _ hx_fin h_pred_fin h_pred_strict hx_min h_lt
  · -- r = x.value: distance 0.
    rw [h_eq]; simp; linarith
  · -- r > x.value
    have h_abs : |r - x.toRealOrZero| = r - x.toRealOrZero :=
      abs_of_pos (sub_pos.mpr h_gt)
    rw [h_abs]
    cases x with
    | nan => simp [isFinite] at hx_fin
    | inf _ => simp [isFinite] at hx_fin
    | finite s e m =>
      by_cases h_max_pos : s = false ∧ e.val = 2 ^ eb - 2 ∧ m.val = 2 ^ mb - 1
      · -- max_pos: r > x.value + ulp/2 = overflowBoundary, contradicts hover.
        obtain ⟨hs, he, hm⟩ := h_max_pos
        have h_2eb : (2 : Nat) ^ 2 ≤ 2 ^ eb := Nat.pow_le_pow_right (by decide) heb
        have h_e_ne : e.val ≠ 0 := by rw [he]; omega
        have h_e_int : (e.val : Int) = (2 : Int) ^ eb - 2 := by
          rw [show (e.val : Int) = ((e.val : Nat) : Int) from rfl, he,
              Nat.cast_sub (by omega : (2 : Nat) ≤ 2 ^ eb)]
          push_cast; rfl
        have h_e_minus_bias : (e.val : Int) - bias eb = maxExp eb := by
          rw [h_e_int]
          unfold maxExp bias
          have h_split : (2 : Int) ^ eb = 2 * (2 : Int) ^ (eb - 1) := by
            calc (2 : Int) ^ eb
                = (2 : Int) ^ ((eb - 1) + 1) := by
                  rw [Nat.sub_add_cancel (by omega : 1 ≤ eb)]
              _ = (2 : Int) ^ (eb - 1) * 2 := pow_succ _ _
              _ = 2 * (2 : Int) ^ (eb - 1) := by ring
          rw [h_split]; ring
        have h_x_val : (.finite s e m : IEEEFloat eb mb).toRealOrZero = maxFinite eb mb := by
          rw [hs, toRealOrZero_finite_eq]
          unfold finiteValue maxFinite
          rw [if_neg h_e_ne]
          simp only [show (if (false : Bool) = true then (-1 : ℝ) else 1) = 1 from rfl, one_mul]
          rw [show (m.val : ℝ) = (2 : ℝ) ^ mb - 1 by
              rw [show (m.val : ℝ) = ((m.val : Nat) : ℝ) from rfl, hm,
                  cast_two_pow_sub_one]]
          rw [h_e_minus_bias, zpow_neg, zpow_natCast]
          field_simp
          ring
        have h_x_ulp : (.finite s e m : IEEEFloat eb mb).ulp = topUlp eb mb := by
          show (if e.val = 0 then (2 : ℝ) ^ minSubnormalExp eb mb
                else (2 : ℝ) ^ ((e.val : Int) - bias eb - (mb : Int))) = topUlp eb mb
          rw [if_neg h_e_ne]
          rw [show (e.val : Int) - bias eb - (mb : Int) = maxExp eb - (mb : Int) by
              rw [h_e_minus_bias]]
          rfl
        rw [h_x_val, h_x_ulp]
        -- maxFinite + topUlp/2 = overflowBoundary by definition.
        -- r > maxFinite ≥ 0; |r| < overflowBoundary; so r < overflowBoundary.
        have h_max_finite_pos : 0 < maxFinite eb mb := by
          unfold maxFinite
          have h_mb_pow_ge : (1 : ℝ) ≤ (2 : ℝ) ^ mb := one_le_pow₀ (by norm_num)
          have h_neg_le_one : (2 : ℝ) ^ (-(mb : Int)) ≤ 1 := by
            rw [zpow_neg, zpow_natCast]
            exact inv_le_one_of_one_le₀ h_mb_pow_ge
          have h_factor_pos : (0 : ℝ) < 2 - (2 : ℝ) ^ (-(mb : Int)) := by linarith
          have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ maxExp eb := zpow_pos (by norm_num) _
          exact mul_pos h_factor_pos h_pow_pos
        have h_r_pos : 0 ≤ r := by
          rw [h_x_val] at h_gt
          linarith
        have h_r_abs : |r| = r := abs_of_nonneg h_r_pos
        rw [h_r_abs] at hover
        -- hover : r < overflowBoundary = maxFinite + topUlp/2
        unfold overflowBoundary at hover
        linarith
      · by_cases h_neg_zero : s = true ∧ e.val = 0 ∧ m.val = 0
        · -- x = -0: nextFinite (-0) = +0 (same value).  Use +smallest_sub directly.
          obtain ⟨hs, he, hm⟩ := h_neg_zero
          have h_e_pos : 0 < 2 ^ eb - 1 := by
            have := e.isLt; rw [he] at this; exact this
          have h_m_two : 1 < 2 ^ mb := by
            have h2 : 2 ^ 1 ≤ 2 ^ mb := Nat.pow_le_pow_right (by decide) hmb
            omega
          have h_zero_lt_mb : 0 < 2 ^ mb := Nat.pow_pos (by decide)
          let y : IEEEFloat eb mb := .finite false ⟨0, h_e_pos⟩ ⟨1, h_m_two⟩
          have hy_fin : y.isFinite = true := rfl
          have hy_val : y.toRealOrZero = (2 : ℝ) ^ minSubnormalExp eb mb := by
            show finiteValue false (⟨0, h_e_pos⟩ : Fin (2 ^ eb - 1))
                                   (⟨1, h_m_two⟩ : Fin (2 ^ mb))
              = (2 : ℝ) ^ minSubnormalExp eb mb
            simp only [finiteValue, ↓reduceIte]
            rw [show minSubnormalExp eb mb = minNormalExp eb - (mb : Int) from rfl,
                zpow_sub_natCast]
            push_cast; ring
          have hx_val : (.finite s e m : IEEEFloat eb mb).toRealOrZero = 0 := by
            rw [hs, toRealOrZero_finite_eq]
            have h_m0 : m.val = 0 := hm
            have h_e0 : e.val = 0 := he
            have he_cast : e = (⟨0, h_e_pos⟩ : Fin (2 ^ eb - 1)) := Fin.ext h_e0
            have hm_cast : m = (⟨0, h_zero_lt_mb⟩ : Fin (2 ^ mb)) := Fin.ext h_m0
            rw [he_cast, hm_cast]
            exact finiteValue_zero_neg h_e_pos h_zero_lt_mb
          have hx_ulp : (.finite s e m : IEEEFloat eb mb).ulp
                      = (2 : ℝ) ^ minSubnormalExp eb mb := by
            simp [ulp, he]
          have hxy := hx_min y hy_fin
          rw [hx_val, hy_val] at hxy
          have h_r_pos : 0 < r := by rw [← hx_val]; exact h_gt
          have h_x_abs : |(0 : ℝ) - r| = r := by
            rw [zero_sub, abs_neg, abs_of_pos h_r_pos]
          rw [h_x_abs] at hxy
          have h_2pow_pos : (0 : ℝ) < (2 : ℝ) ^ minSubnormalExp eb mb :=
            zpow_pos (by norm_num) _
          rw [hx_val, hx_ulp]
          by_cases h_r_le : r ≤ (2 : ℝ) ^ minSubnormalExp eb mb
          · have h_y_abs : |(2 : ℝ) ^ minSubnormalExp eb mb - r|
                         = (2 : ℝ) ^ minSubnormalExp eb mb - r :=
              abs_of_nonneg (by linarith)
            rw [h_y_abs] at hxy
            linarith
          · push_neg at h_r_le
            exfalso
            have h_y_abs : |(2 : ℝ) ^ minSubnormalExp eb mb - r|
                         = r - (2 : ℝ) ^ minSubnormalExp eb mb := by
              rw [abs_sub_comm]; exact abs_of_pos (by linarith)
            rw [h_y_abs] at hxy
            linarith
        · -- Generic: use nextFinite x.
          have h_succ_fin : (nextFinite (.finite s e m : IEEEFloat eb mb)).isFinite = true := by
            cases s with
            | false =>
              simp only [nextFinite]
              by_cases h1 : m.val + 1 < 2 ^ mb
              · simp [h1, isFinite]
              · by_cases h2 : e.val + 1 < 2 ^ eb - 1
                · simp [h1, h2, isFinite]
                · exfalso
                  push_neg at h1 h2
                  apply h_max_pos
                  refine ⟨rfl, ?_, ?_⟩
                  · have := e.isLt; omega
                  · have := m.isLt; omega
            | true =>
              simp only [nextFinite]
              by_cases h1 : m.val ≠ 0
              · simp [h1, isFinite]
              · by_cases h2 : e.val ≠ 0
                · simp [h1, h2, isFinite]
                · simp [h1, h2, isFinite]
          have h_succ_strict : (.finite s e m : IEEEFloat eb mb).toRealOrZero
                              < (nextFinite (.finite s e m : IEEEFloat eb mb)).toRealOrZero := by
            cases s with
            | false =>
              simp only [nextFinite]
              by_cases h1 : m.val + 1 < 2 ^ mb
              · simp only [dif_pos h1]
                exact nextFinite_value_lt_pos_within e m h1
              · by_cases h2 : e.val + 1 < 2 ^ eb - 1
                · simp only [dif_neg h1, dif_pos h2]
                  exact nextFinite_value_lt_pos_cross e m h1 h2
                · exfalso
                  push_neg at h1 h2
                  apply h_max_pos
                  refine ⟨rfl, ?_, ?_⟩
                  · have := e.isLt; omega
                  · have := m.isLt; omega
            | true =>
              simp only [nextFinite]
              by_cases h1 : m.val ≠ 0
              · simp only [dif_pos h1]
                exact nextFinite_value_lt_neg_within e m h1
              · by_cases h2 : e.val ≠ 0
                · simp only [dif_neg h1, dif_pos h2]
                  exact nextFinite_value_lt_neg_cross e m h1 h2
                · exfalso
                  push_neg at h1 h2
                  apply h_neg_zero
                  exact ⟨rfl, h2, h1⟩
          exact half_ulp_bound_above r _ hx_fin h_succ_fin h_succ_strict hx_min h_gt

end IEEEFloat
