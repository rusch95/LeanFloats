import IEEEFloat.Arith
import IEEEFloat.RoundExistence

/-! # Constructive RNE arithmetic backend

This module provides constructive (but `noncomputable` — `ℝ` is)
implementations of `add`, `sub`, `mul`, and `div`, along with the
proofs that each satisfies the corresponding `IsCorrectlyRounded*`
contract from `IEEEFloat.Arith`.

The design pattern is simple:

  *  Pattern-match on the constructors of the operands to dispatch
     the IEEE 754 §6 special-case rules (NaN propagation, ±∞
     arithmetic, signed-zero edge cases).
  *  For genuinely finite operand pairs, delegate to
     `roundToNearestEven` (from `IEEEFloat.RoundExistence`) over the
     exact real-valued result.

Because `roundToNearestEven` is itself defined via `Classical.choose`,
the resulting backend is not extractable — but it *is* a single
explicit term, not a hidden choice, so downstream proofs can
unfold it.

Each of the four ops returns a value satisfying its
`IsCorrectlyRounded*` predicate (theorems
`add_isCorrectlyRounded` etc.), establishing that downstream
consumers parameterised over `[Add F]` / `[Mul F]` style typeclasses
can be instantiated against this backend without further work.
-/

namespace IEEEFloat

variable {eb mb : Nat}

/-! ## Addition -/

/-- Constructive RNE addition. -/
noncomputable def add (heb : 1 ≤ eb) (hmb : 1 ≤ mb)
    (x y : IEEEFloat eb mb) : IEEEFloat eb mb :=
  match x, y with
  | .nan, _ => .nan
  | _, .nan => .nan
  | .inf sx, .inf sy => if sx = sy then .inf sx else .nan
  | .inf s, .finite _ _ _ => .inf s
  | .finite _ _ _, .inf s => .inf s
  | .finite sx ex mx, .finite sy ey my =>
      roundToNearestEven heb hmb (finiteValue sx ex mx + finiteValue sy ey my)

theorem add_isCorrectlyRounded (heb : 1 ≤ eb) (hmb : 1 ≤ mb)
    (x y : IEEEFloat eb mb) :
    IsCorrectlyRoundedAdd x y (add heb hmb x y) where
  nan_prop := by
    rintro (rfl | rfl)
    · rfl
    · cases x <;> rfl
  inf_minus_inf := by
    intro hx hy hsign
    cases x with
    | nan => cases hx
    | finite _ _ _ => cases hx
    | inf sx =>
      cases y with
      | nan => cases hy
      | finite _ _ _ => cases hy
      | inf sy =>
        simp only [signBit] at hsign
        simp [add, hsign]
  inf_same_sign := by
    intro hx hy hsign
    cases x with
    | nan => cases hx
    | finite _ _ _ => cases hx
    | inf sx =>
      cases y with
      | nan => cases hy
      | finite _ _ _ => cases hy
      | inf sy =>
        simp only [signBit] at hsign
        subst hsign
        simp [add]
  inf_left := by
    intro hx hy
    cases x with
    | nan => cases hx
    | finite _ _ _ => cases hx
    | inf sx =>
      cases y with
      | nan => cases hy
      | inf _ => cases hy
      | finite _ _ _ => rfl
  inf_right := by
    intro hx hy
    cases x with
    | nan => cases hx
    | inf _ => cases hx
    | finite _ _ _ =>
      cases y with
      | nan => cases hy
      | finite _ _ _ => cases hy
      | inf _ => rfl
  rne_of_sum := by
    intro ra rb hra hrb
    cases x with
    | nan => simp [toReal] at hra
    | inf _ => simp [toReal] at hra
    | finite sx ex mx =>
      cases y with
      | nan => simp [toReal] at hrb
      | inf _ => simp [toReal] at hrb
      | finite sy ey my =>
        simp [toReal] at hra hrb
        subst hra; subst hrb
        unfold add
        exact roundToNearestEven_isRNE heb hmb _

/-! ## Subtraction -/

/-- Constructive RNE subtraction. -/
noncomputable def sub (heb : 1 ≤ eb) (hmb : 1 ≤ mb)
    (x y : IEEEFloat eb mb) : IEEEFloat eb mb :=
  match x, y with
  | .nan, _ => .nan
  | _, .nan => .nan
  | .inf sx, .inf sy => if sx = sy then .nan else .inf sx
  | .inf s, .finite _ _ _ => .inf s
  | .finite _ _ _, .inf s => .inf (!s)
  | .finite sx ex mx, .finite sy ey my =>
      roundToNearestEven heb hmb (finiteValue sx ex mx - finiteValue sy ey my)

theorem sub_isCorrectlyRounded (heb : 1 ≤ eb) (hmb : 1 ≤ mb)
    (x y : IEEEFloat eb mb) :
    IsCorrectlyRoundedSub x y (sub heb hmb x y) where
  nan_prop := by
    rintro (rfl | rfl)
    · rfl
    · cases x <;> rfl
  inf_same_sign := by
    intro hx hy hsign
    cases x with
    | nan => cases hx
    | finite _ _ _ => cases hx
    | inf sx =>
      cases y with
      | nan => cases hy
      | finite _ _ _ => cases hy
      | inf sy =>
        simp only [signBit] at hsign
        subst hsign
        simp [sub]
  inf_diff_sign := by
    intro hx hy hsign
    cases x with
    | nan => cases hx
    | finite _ _ _ => cases hx
    | inf sx =>
      cases y with
      | nan => cases hy
      | finite _ _ _ => cases hy
      | inf sy =>
        simp only [signBit] at hsign
        simp [sub, hsign]
  inf_left := by
    intro hx hy
    cases x with
    | nan => cases hx
    | finite _ _ _ => cases hx
    | inf sx =>
      cases y with
      | nan => cases hy
      | inf _ => cases hy
      | finite _ _ _ => rfl
  inf_right := by
    intro hx hy
    cases x with
    | nan => cases hx
    | inf _ => cases hx
    | finite _ _ _ =>
      cases y with
      | nan => cases hy
      | finite _ _ _ => cases hy
      | inf _ => rfl
  rne_of_diff := by
    intro ra rb hra hrb
    cases x with
    | nan => simp [toReal] at hra
    | inf _ => simp [toReal] at hra
    | finite sx ex mx =>
      cases y with
      | nan => simp [toReal] at hrb
      | inf _ => simp [toReal] at hrb
      | finite sy ey my =>
        simp [toReal] at hra hrb
        subst hra; subst hrb
        unfold sub
        exact roundToNearestEven_isRNE heb hmb _

/-! ## Multiplication -/

/-- Constructive RNE multiplication. -/
noncomputable def mul (heb : 1 ≤ eb) (hmb : 1 ≤ mb)
    (x y : IEEEFloat eb mb) : IEEEFloat eb mb :=
  match x, y with
  | .nan, _ => .nan
  | _, .nan => .nan
  | .inf sx, .inf sy => .inf (sx != sy)
  | .inf sx, .finite sy ey my =>
      if (IEEEFloat.finite sy ey my : IEEEFloat eb mb).isZero
      then .nan else .inf (sx != sy)
  | .finite sx ex mx, .inf sy =>
      if (IEEEFloat.finite sx ex mx : IEEEFloat eb mb).isZero
      then .nan else .inf (sx != sy)
  | .finite sx ex mx, .finite sy ey my =>
      roundToNearestEven heb hmb (finiteValue sx ex mx * finiteValue sy ey my)

theorem mul_isCorrectlyRounded (heb : 1 ≤ eb) (hmb : 1 ≤ mb)
    (x y : IEEEFloat eb mb) :
    IsCorrectlyRoundedMul x y (mul heb hmb x y) where
  nan_prop := by
    rintro (rfl | rfl)
    · rfl
    · cases x <;> rfl
  zero_times_inf := by
    rintro (⟨hxz, hyi⟩ | ⟨hxi, hyz⟩)
    · cases x with
      | nan => cases hxz
      | inf _ => cases hxz
      | finite _ _ _ =>
        cases y with
        | nan => cases hyi
        | finite _ _ _ => cases hyi
        | inf _ => simp [mul, hxz]
    · cases x with
      | nan => cases hxi
      | finite _ _ _ => cases hxi
      | inf _ =>
        cases y with
        | nan => cases hyz
        | inf _ => cases hyz
        | finite _ _ _ => simp [mul, hyz]
  inf_times_finite := by
    intro hx hy hyz
    cases x with
    | nan => cases hx
    | finite _ _ _ => cases hx
    | inf sx =>
      cases y with
      | nan => cases hy
      | inf _ => cases hy
      | finite sy ey my =>
        simp only [signBit, mul]
        rw [if_neg (by simp [hyz])]
  finite_times_inf := by
    intro hx hxz hy
    cases x with
    | nan => cases hx
    | inf _ => cases hx
    | finite sx ex mx =>
      cases y with
      | nan => cases hy
      | finite _ _ _ => cases hy
      | inf sy =>
        simp only [signBit, mul]
        rw [if_neg (by simp [hxz])]
  inf_times_inf := by
    intro hx hy
    cases x with
    | nan => cases hx
    | finite _ _ _ => cases hx
    | inf sx =>
      cases y with
      | nan => cases hy
      | finite _ _ _ => cases hy
      | inf sy => rfl
  rne_of_product := by
    intro ra rb hra hrb
    cases x with
    | nan => simp [toReal] at hra
    | inf _ => simp [toReal] at hra
    | finite sx ex mx =>
      cases y with
      | nan => simp [toReal] at hrb
      | inf _ => simp [toReal] at hrb
      | finite sy ey my =>
        simp [toReal] at hra hrb
        subst hra; subst hrb
        unfold mul
        exact roundToNearestEven_isRNE heb hmb _

/-! ## Division -/

/-- Constructive RNE division.

`±∞ / 0` follows the same sign-xor rule as `±∞ / finite_nonzero` —
the `IsCorrectlyRoundedDiv` structure leaves this case unconstrained,
but consistency with `1 / 0 = ±∞` makes this the natural choice. -/
noncomputable def div (heb : 1 ≤ eb) (hmb : 1 ≤ mb)
    (x y : IEEEFloat eb mb) : IEEEFloat eb mb :=
  match x, y with
  | .nan, _ => .nan
  | _, .nan => .nan
  | .inf _, .inf _ => .nan
  | .inf sx, .finite sy _ _ => .inf (sx != sy)
  | .finite sx _ _, .inf sy =>
      .finite (sx != sy)
        ⟨0, by
          have h : 2 ^ 1 ≤ 2 ^ eb := Nat.pow_le_pow_right (by norm_num) heb
          simp at h; omega⟩
        ⟨0, Nat.one_le_two_pow⟩
  | .finite sx ex mx, .finite sy ey my =>
      if (IEEEFloat.finite sy ey my : IEEEFloat eb mb).isZero
      then
        if (IEEEFloat.finite sx ex mx : IEEEFloat eb mb).isZero
        then .nan
        else .inf (sx != sy)
      else
        roundToNearestEven heb hmb
          (finiteValue sx ex mx / finiteValue sy ey my)

theorem div_isCorrectlyRounded (heb : 1 ≤ eb) (hmb : 1 ≤ mb)
    (x y : IEEEFloat eb mb) :
    IsCorrectlyRoundedDiv x y (div heb hmb x y) where
  nan_prop := by
    rintro (rfl | rfl)
    · rfl
    · cases x <;> rfl
  zero_div_zero := by
    intro hxz hyz
    cases x with
    | nan => cases hxz
    | inf _ => cases hxz
    | finite sx ex mx =>
      cases y with
      | nan => cases hyz
      | inf _ => cases hyz
      | finite sy ey my =>
        simp [div, hxz, hyz]
  inf_div_inf := by
    intro hx hy
    cases x with
    | nan => cases hx
    | finite _ _ _ => cases hx
    | inf _ =>
      cases y with
      | nan => cases hy
      | finite _ _ _ => cases hy
      | inf _ => rfl
  finite_div_zero := by
    intro hx hxz hyz
    cases x with
    | nan => cases hx
    | inf _ => cases hx
    | finite sx ex mx =>
      cases y with
      | nan => cases hyz
      | inf _ => cases hyz
      | finite sy ey my =>
        simp only [signBit, div]
        rw [if_pos hyz, if_neg (by simp [hxz])]
  inf_div_finite := by
    intro hx hy hyz
    cases x with
    | nan => cases hx
    | finite _ _ _ => cases hx
    | inf sx =>
      cases y with
      | nan => cases hy
      | inf _ => cases hy
      | finite sy ey my => rfl
  finite_div_inf := by
    intro hx hy
    cases x with
    | nan => cases hx
    | inf _ => cases hx
    | finite sx ex mx =>
      cases y with
      | nan => cases hy
      | finite _ _ _ => cases hy
      | inf sy =>
        refine ⟨?_, ?_⟩ <;> simp [div, isZero, signBit]
  rne_of_quotient := by
    intro ra rb hra hrb hrb_ne
    cases x with
    | nan => simp [toReal] at hra
    | inf _ => simp [toReal] at hra
    | finite sx ex mx =>
      cases y with
      | nan => simp [toReal] at hrb
      | inf _ => simp [toReal] at hrb
      | finite sy ey my =>
        simp [toReal] at hra hrb
        subst hra; subst hrb
        have h_y_ne_zero : ¬ (IEEEFloat.finite sy ey my : IEEEFloat eb mb).isZero = true := by
          intro h_zero
          apply hrb_ne
          simp [isZero] at h_zero
          obtain ⟨h_e, h_m⟩ := h_zero
          unfold finiteValue
          rcases sy <;> simp [h_e, h_m]
        show IsRoundedToNearestEven _
          (if (IEEEFloat.finite sy ey my : IEEEFloat eb mb).isZero
           then _
           else roundToNearestEven heb hmb (finiteValue sx ex mx / finiteValue sy ey my))
        rw [if_neg h_y_ne_zero]
        exact roundToNearestEven_isRNE heb hmb _

/-! ## Square root -/

/-- Constructive RNE square root.  Follows IEEE 754 §6.3:
  *  `√NaN = NaN`
  *  `√(±0) = ±0` (sign preserved)
  *  `√(+∞) = +∞`, `√(−∞) = NaN`
  *  `√(negative nonzero finite) = NaN`
  *  `√(positive finite) = RNE(√x)` -/
noncomputable def sqrt (heb : 1 ≤ eb) (hmb : 1 ≤ mb)
    (a : IEEEFloat eb mb) : IEEEFloat eb mb :=
  match a with
  | .nan       => .nan
  | .inf false => .inf false
  | .inf true  => .nan
  | .finite s e m =>
    if (IEEEFloat.finite s e m : IEEEFloat eb mb).isZero then
      .finite s e m
    else if s then
      .nan
    else
      roundToNearestEven heb hmb (Real.sqrt (finiteValue s e m))

theorem sqrt_isCorrectlyRounded (heb : 1 ≤ eb) (hmb : 1 ≤ mb)
    (a : IEEEFloat eb mb) :
    IsCorrectlyRoundedSqrt a (sqrt heb hmb a) where
  nan_prop := by rintro rfl; rfl
  sqrt_zero := by
    intro hz
    cases a with
    | nan => cases hz
    | inf _ => cases hz
    | finite s e m =>
      simp only [sqrt]
      rw [if_pos hz]
  sqrt_pos_inf := by rintro rfl; rfl
  sqrt_neg_inf := by rintro rfl; rfl
  sqrt_negative := by
    intro ha hnz hs
    cases a with
    | nan => cases ha
    | inf _ => cases ha
    | finite s e m =>
      simp only [signBit] at hs
      subst hs
      simp only [sqrt]
      rw [if_neg (by simp [hnz])]
      simp
  rne_of_sqrt := by
    intro ra hra hra_pos
    cases a with
    | nan => simp [toReal] at hra
    | inf _ => simp [toReal] at hra
    | finite s e m =>
      simp [toReal] at hra
      subst hra
      simp only [sqrt]
      -- a must be nonzero (since 0 < finiteValue s e m)
      have hz : ¬ (IEEEFloat.finite s e m : IEEEFloat eb mb).isZero = true := by
        intro h_zero
        simp [isZero] at h_zero
        obtain ⟨he, hm⟩ := h_zero
        have : finiteValue s e m = 0 := by
          unfold finiteValue
          rcases s <;> simp [he, hm]
        linarith
      rw [if_neg hz]
      -- a must have positive sign (else value would be negative)
      rcases s with _ | _
      · rw [if_neg (by simp)]
        exact roundToNearestEven_isRNE heb hmb _
      · -- s = true: finiteValue is non-positive, contradicts hra_pos
        exfalso
        have h_nn : finiteValue true e m ≤ 0 := by
          unfold finiteValue
          simp
          split_ifs with h_e
          · have h_2pow_z : (0 : ℝ) ≤ (2 : ℝ) ^ minNormalExp eb :=
              le_of_lt (zpow_pos (by norm_num) _)
            have h_div : (0 : ℝ) ≤ (m.val : ℝ) / 2 ^ mb := by positivity
            have : (0 : ℝ) ≤ 2 ^ minNormalExp eb * ((m.val : ℝ) / 2 ^ mb) :=
              mul_nonneg h_2pow_z h_div
            linarith
          · have h_2pow : (0 : ℝ) < (2 : ℝ) ^ ((e.val : Int) - bias eb) :=
              zpow_pos (by norm_num) _
            have h_one_plus : (0 : ℝ) < 1 + (m.val : ℝ) / 2 ^ mb := by positivity
            have : (0 : ℝ) <
                2 ^ ((e.val : Int) - bias eb) * (1 + (m.val : ℝ) / 2 ^ mb) :=
              mul_pos h_2pow h_one_plus
            linarith
        linarith

/-! ## Fused multiply-add -/

/-- Constructive RNE fused multiply-add: single rounding on `a*b + c`,
    no intermediate rounding. -/
noncomputable def fma (heb : 1 ≤ eb) (hmb : 1 ≤ mb)
    (a b c : IEEEFloat eb mb) : IEEEFloat eb mb :=
  match a, b, c with
  | .nan, _, _ => .nan
  | _, .nan, _ => .nan
  | _, _, .nan => .nan
  | .inf sa, .inf sb, .inf sc =>
      if (sa != sb) = sc then .inf sc else .nan
  | .inf sa, .inf sb, .finite _ _ _ => .inf (sa != sb)
  | .inf sa, .finite sb eb_ mb_, c =>
      if (IEEEFloat.finite sb eb_ mb_ : IEEEFloat eb mb).isZero then .nan
      else
        match c with
        | .inf sc => if (sa != sb) = sc then .inf sc else .nan
        | .finite _ _ _ => .inf (sa != sb)
        | .nan => .nan
  | .finite sa ea ma, .inf sb, c =>
      if (IEEEFloat.finite sa ea ma : IEEEFloat eb mb).isZero then .nan
      else
        match c with
        | .inf sc => if (sa != sb) = sc then .inf sc else .nan
        | .finite _ _ _ => .inf (sa != sb)
        | .nan => .nan
  | .finite _ _ _, .finite _ _ _, .inf sc => .inf sc
  | .finite sa ea ma, .finite sb eb_ mb_, .finite sc ec mc =>
      roundToNearestEven heb hmb
        (finiteValue sa ea ma * finiteValue sb eb_ mb_ + finiteValue sc ec mc)

theorem fma_isCorrectlyRounded (heb : 1 ≤ eb) (hmb : 1 ≤ mb)
    (a b c : IEEEFloat eb mb) :
    IsCorrectlyRoundedFma a b c (fma heb hmb a b c) where
  nan_prop := by
    rintro (rfl | rfl | rfl)
    · rfl
    · cases a <;> rfl
    · cases a <;> cases b <;> rfl
  zero_times_inf := by
    rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · cases a with
      | nan => cases ha
      | inf _ => cases ha
      | finite sa ea ma =>
        cases b with
        | nan => cases hb
        | finite _ _ _ => cases hb
        | inf sb =>
          cases c with
          | nan => rfl
          | inf _ => simp [fma, ha]
          | finite _ _ _ => simp [fma, ha]
    · cases a with
      | nan => cases ha
      | finite _ _ _ => cases ha
      | inf sa =>
        cases b with
        | nan => cases hb
        | inf _ => cases hb
        | finite sb eb_ mb_ =>
          cases c with
          | nan => rfl
          | inf _ => simp [fma, hb]
          | finite _ _ _ => simp [fma, hb]
  inf_mult_inf_match := by
    intro h_inf_mult hc h_match
    rcases h_inf_mult with ⟨ha, hb⟩ | ⟨ha, hb, hbz⟩ | ⟨ha, haz, hb⟩
    · cases a with
      | nan => cases ha
      | finite _ _ _ => cases ha
      | inf sa =>
        cases b with
        | nan => cases hb
        | finite _ _ _ => cases hb
        | inf sb =>
          cases c with
          | nan => cases hc
          | finite _ _ _ => cases hc
          | inf sc =>
            simp only [signBit] at h_match
            simp [fma, signBit, h_match]
    · cases a with
      | nan => cases ha
      | finite _ _ _ => cases ha
      | inf sa =>
        cases b with
        | nan => cases hb
        | inf _ => cases hb
        | finite sb eb_ mb_ =>
          cases c with
          | nan => cases hc
          | finite _ _ _ => cases hc
          | inf sc =>
            simp only [signBit] at h_match
            simp [fma, signBit, hbz, h_match]
    · cases a with
      | nan => cases ha
      | inf _ => cases ha
      | finite sa ea ma =>
        cases b with
        | nan => cases hb
        | finite _ _ _ => cases hb
        | inf sb =>
          cases c with
          | nan => cases hc
          | finite _ _ _ => cases hc
          | inf sc =>
            simp only [signBit] at h_match
            simp [fma, signBit, haz, h_match]
  inf_mult_inf_diff := by
    intro h_inf_mult hc h_diff
    rcases h_inf_mult with ⟨ha, hb⟩ | ⟨ha, hb, hbz⟩ | ⟨ha, haz, hb⟩
    · cases a with
      | nan => cases ha
      | finite _ _ _ => cases ha
      | inf sa =>
        cases b with
        | nan => cases hb
        | finite _ _ _ => cases hb
        | inf sb =>
          cases c with
          | nan => cases hc
          | finite _ _ _ => cases hc
          | inf sc =>
            simp only [signBit] at h_diff
            simp [fma, h_diff]
    · cases a with
      | nan => cases ha
      | finite _ _ _ => cases ha
      | inf sa =>
        cases b with
        | nan => cases hb
        | inf _ => cases hb
        | finite sb eb_ mb_ =>
          cases c with
          | nan => cases hc
          | finite _ _ _ => cases hc
          | inf sc =>
            simp only [signBit] at h_diff
            simp [fma, hbz, h_diff]
    · cases a with
      | nan => cases ha
      | inf _ => cases ha
      | finite sa ea ma =>
        cases b with
        | nan => cases hb
        | finite _ _ _ => cases hb
        | inf sb =>
          cases c with
          | nan => cases hc
          | finite _ _ _ => cases hc
          | inf sc =>
            simp only [signBit] at h_diff
            simp [fma, haz, h_diff]
  inf_mult_finite := by
    intro h_inf_mult hc
    rcases h_inf_mult with ⟨ha, hb⟩ | ⟨ha, hb, hbz⟩ | ⟨ha, haz, hb⟩
    · cases a with
      | nan => cases ha
      | finite _ _ _ => cases ha
      | inf sa =>
        cases b with
        | nan => cases hb
        | finite _ _ _ => cases hb
        | inf sb =>
          cases c with
          | nan => cases hc
          | inf _ => cases hc
          | finite _ _ _ => rfl
    · cases a with
      | nan => cases ha
      | finite _ _ _ => cases ha
      | inf sa =>
        cases b with
        | nan => cases hb
        | inf _ => cases hb
        | finite sb eb_ mb_ =>
          cases c with
          | nan => cases hc
          | inf _ => cases hc
          | finite _ _ _ =>
            simp only [signBit, fma]
            rw [if_neg (by simp [hbz])]
    · cases a with
      | nan => cases ha
      | inf _ => cases ha
      | finite sa ea ma =>
        cases b with
        | nan => cases hb
        | finite _ _ _ => cases hb
        | inf sb =>
          cases c with
          | nan => cases hc
          | inf _ => cases hc
          | finite _ _ _ =>
            simp only [signBit, fma]
            rw [if_neg (by simp [haz])]
  finite_finite_inf := by
    intro ha hb hc
    cases a with
    | nan => cases ha
    | inf _ => cases ha
    | finite _ _ _ =>
      cases b with
      | nan => cases hb
      | inf _ => cases hb
      | finite _ _ _ =>
        cases c with
        | nan => cases hc
        | finite _ _ _ => cases hc
        | inf _ => rfl
  rne_of_fma := by
    intro ra rb rc hra hrb hrc
    cases a with
    | nan => simp [toReal] at hra
    | inf _ => simp [toReal] at hra
    | finite sa ea ma =>
      cases b with
      | nan => simp [toReal] at hrb
      | inf _ => simp [toReal] at hrb
      | finite sb eb_ mb_ =>
        cases c with
        | nan => simp [toReal] at hrc
        | inf _ => simp [toReal] at hrc
        | finite sc ec mc =>
          simp [toReal] at hra hrb hrc
          subst hra; subst hrb; subst hrc
          unfold fma
          exact roundToNearestEven_isRNE heb hmb _

end IEEEFloat
