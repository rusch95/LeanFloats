import IEEEFloat.Backend
import IEEEFloat.Compare

/-! # Foundational identity lemmas

The "obvious facts" downstream proofs reach for repeatedly:

  *  Cross-relations between `isNaN`, `isInf`, `isFinite`, `isZero`,
     `isSubnormal`, `isNormal`.
  *  How negation interacts with each predicate, the sign bit, and
     `toRealOrZero`.
  *  Real values of canonical encodings (`±0`, `±∞`, `NaN` all read
     as `0` through `toRealOrZero`).
  *  Constructor distinctness.
  *  Arithmetic special-case identities pinned down by the
     `IsCorrectlyRounded*` contracts (`add` of `±∞` and finite,
     `mul` involving zero, etc.).
  *  Comparison properties (`eq_comm`, `lt_asymm`, `unordered_eq`).

This module establishes those facts in one place so consumers can
`simp [Identities]` instead of re-deriving each inline.
-/

namespace IEEEFloat

variable {eb mb : Nat}

/-! ## Predicate cross-relations -/

theorem isFinite_or_isInf_or_isNaN (x : IEEEFloat eb mb) :
    x.isFinite = true ∨ x.isInf = true ∨ x.isNaN = true := by
  cases x <;> simp [isFinite, isInf, isNaN]

theorem isNaN_iff_not_isFinite_not_isInf (x : IEEEFloat eb mb) :
    x.isNaN = true ↔ x.isFinite = false ∧ x.isInf = false := by
  cases x <;> simp [isNaN, isFinite, isInf]

theorem isFinite_iff_not_isNaN_not_isInf (x : IEEEFloat eb mb) :
    x.isFinite = true ↔ x.isNaN = false ∧ x.isInf = false := by
  cases x <;> simp [isNaN, isFinite, isInf]

theorem isInf_iff_not_isNaN_not_isFinite (x : IEEEFloat eb mb) :
    x.isInf = true ↔ x.isNaN = false ∧ x.isFinite = false := by
  cases x <;> simp [isNaN, isFinite, isInf]

theorem isZero_imp_isFinite (x : IEEEFloat eb mb) :
    x.isZero = true → x.isFinite = true := by
  cases x <;> simp [isZero, isFinite]

theorem isSubnormal_imp_isFinite (x : IEEEFloat eb mb) :
    x.isSubnormal = true → x.isFinite = true := by
  cases x <;> simp [isSubnormal, isFinite]

theorem isNormal_imp_isFinite (x : IEEEFloat eb mb) :
    x.isNormal = true → x.isFinite = true := by
  cases x <;> simp [isNormal, isFinite]

theorem not_isZero_isNormal (x : IEEEFloat eb mb) :
    ¬ (x.isZero = true ∧ x.isNormal = true) := by
  rintro ⟨hz, hn⟩
  cases x with
  | nan => cases hz
  | inf _ => cases hz
  | finite s e m =>
    simp [isZero] at hz
    simp [isNormal] at hn
    exact hn hz.1

theorem not_isZero_isSubnormal (x : IEEEFloat eb mb) :
    ¬ (x.isZero = true ∧ x.isSubnormal = true) := by
  rintro ⟨hz, hs⟩
  cases x with
  | nan => cases hz
  | inf _ => cases hz
  | finite s e m =>
    simp [isZero] at hz
    simp [isSubnormal] at hs
    exact hs.2 hz.2

theorem not_isSubnormal_isNormal (x : IEEEFloat eb mb) :
    ¬ (x.isSubnormal = true ∧ x.isNormal = true) := by
  rintro ⟨hs, hn⟩
  cases x with
  | nan => cases hs
  | inf _ => cases hs
  | finite s e m =>
    simp [isSubnormal] at hs
    simp [isNormal] at hn
    exact hn hs.1

/-- For finite values, `isZero ∨ isSubnormal ∨ isNormal` is exhaustive
    and mutually exclusive. -/
theorem finite_trichotomy (x : IEEEFloat eb mb) (hx : x.isFinite = true) :
    x.isZero = true ∨ x.isSubnormal = true ∨ x.isNormal = true := by
  cases x with
  | nan => cases hx
  | inf _ => cases hx
  | finite s e m =>
    by_cases h_e : e.val = 0
    · by_cases h_m : m.val = 0
      · left; simp [isZero, h_e, h_m]
      · right; left; simp [isSubnormal, h_e, h_m]
    · right; right; simp [isNormal, h_e]

/-! ## Constructor distinctness -/

@[simp] theorem nan_ne_inf (s : Bool) :
    (.nan : IEEEFloat eb mb) ≠ .inf s := fun h => by cases h
@[simp] theorem inf_ne_nan (s : Bool) :
    (.inf s : IEEEFloat eb mb) ≠ .nan := fun h => by cases h

@[simp] theorem nan_ne_finite (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    (.nan : IEEEFloat eb mb) ≠ .finite s e m := fun h => by cases h
@[simp] theorem finite_ne_nan (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    (.finite s e m : IEEEFloat eb mb) ≠ .nan := fun h => by cases h

@[simp] theorem inf_ne_finite (s s' : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    (.inf s : IEEEFloat eb mb) ≠ .finite s' e m := fun h => by cases h
@[simp] theorem finite_ne_inf (s s' : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    (.finite s e m : IEEEFloat eb mb) ≠ .inf s' := fun h => by cases h

/-! ## Negation -/

@[simp] theorem isNaN_neg (x : IEEEFloat eb mb) : (-x).isNaN = x.isNaN := by
  cases x <;> rfl

@[simp] theorem isInf_neg (x : IEEEFloat eb mb) : (-x).isInf = x.isInf := by
  cases x <;> rfl

@[simp] theorem isFinite_neg (x : IEEEFloat eb mb) : (-x).isFinite = x.isFinite := by
  cases x <;> rfl

@[simp] theorem isZero_neg (x : IEEEFloat eb mb) : (-x).isZero = x.isZero := by
  cases x <;> rfl

@[simp] theorem isSubnormal_neg (x : IEEEFloat eb mb) :
    (-x).isSubnormal = x.isSubnormal := by
  cases x <;> rfl

@[simp] theorem isNormal_neg (x : IEEEFloat eb mb) :
    (-x).isNormal = x.isNormal := by
  cases x <;> rfl

theorem signBit_neg_non_nan (x : IEEEFloat eb mb) (hx : x ≠ .nan) :
    (-x).signBit = !x.signBit := by
  cases x with
  | nan => exact absurd rfl hx
  | inf _ => rfl
  | finite _ _ _ => rfl

theorem toRealOrZero_neg (x : IEEEFloat eb mb) :
    (-x).toRealOrZero = -(x.toRealOrZero) := by
  cases x with
  | nan => show (0 : ℝ) = -0; ring
  | inf _ => show (0 : ℝ) = -0; ring
  | finite s e m =>
    show finiteValue (!s) e m = -(finiteValue s e m)
    unfold finiteValue
    rcases s with _ | _ <;> simp <;> split_ifs <;> ring

theorem toRealOrZero_isZero (x : IEEEFloat eb mb) (hx : x.isZero = true) :
    x.toRealOrZero = 0 := by
  cases x with
  | nan => cases hx
  | inf _ => cases hx
  | finite s e m =>
    simp [isZero] at hx
    show finiteValue _ _ _ = 0
    unfold finiteValue
    rcases s <;> simp [hx.1, hx.2]

/-! ## Sign bit -/

@[simp] theorem signBit_nan : (.nan : IEEEFloat eb mb).signBit = false := rfl
@[simp] theorem signBit_inf (s : Bool) :
    ((.inf s) : IEEEFloat eb mb).signBit = s := rfl
@[simp] theorem signBit_finite (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    (.finite s e m : IEEEFloat eb mb).signBit = s := rfl

/-! ## Comparison -/

theorem unordered_eq_isNaN_or_isNaN (x y : IEEEFloat eb mb) :
    unordered x y = true ↔ x.isNaN = true ∨ y.isNaN = true := by
  cases x <;> cases y <;> simp [unordered, isNaN]

theorem le_refl_non_nan (x : IEEEFloat eb mb) (hx : x ≠ .nan) : le x x = true := by
  unfold le
  rw [eq_self x hx]
  simp

/-! ## Arithmetic special cases (constructor-pinned) -/

section Arithmetic
variable (heb : 1 ≤ eb) (hmb : 1 ≤ mb)

@[simp] theorem add_nan_left (y : IEEEFloat eb mb) :
    add heb hmb .nan y = .nan := rfl
@[simp] theorem add_nan_right (x : IEEEFloat eb mb) :
    add heb hmb x .nan = .nan := by cases x <;> rfl

@[simp] theorem sub_nan_left (y : IEEEFloat eb mb) :
    sub heb hmb .nan y = .nan := rfl
@[simp] theorem sub_nan_right (x : IEEEFloat eb mb) :
    sub heb hmb x .nan = .nan := by cases x <;> rfl

@[simp] theorem mul_nan_left (y : IEEEFloat eb mb) :
    mul heb hmb .nan y = .nan := rfl
@[simp] theorem mul_nan_right (x : IEEEFloat eb mb) :
    mul heb hmb x .nan = .nan := by cases x <;> rfl

@[simp] theorem div_nan_left (y : IEEEFloat eb mb) :
    div heb hmb .nan y = .nan := rfl
@[simp] theorem div_nan_right (x : IEEEFloat eb mb) :
    div heb hmb x .nan = .nan := by cases x <;> rfl

@[simp] theorem fma_nan_first (b c : IEEEFloat eb mb) :
    fma heb hmb .nan b c = .nan := rfl
@[simp] theorem fma_nan_second (a c : IEEEFloat eb mb) :
    fma heb hmb a .nan c = .nan := by cases a <;> rfl
@[simp] theorem fma_nan_third (a b : IEEEFloat eb mb) :
    fma heb hmb a b .nan = .nan := by cases a <;> cases b <;> rfl

theorem add_inf_finite (s : Bool) (y : IEEEFloat eb mb)
    (hy : y.isFinite = true) :
    add heb hmb (.inf s) y = .inf s := by
  cases y with
  | nan => cases hy
  | inf _ => cases hy
  | finite _ _ _ => rfl

theorem add_finite_inf (s : Bool) (x : IEEEFloat eb mb)
    (hx : x.isFinite = true) :
    add heb hmb x (.inf s) = .inf s := by
  cases x with
  | nan => cases hx
  | inf _ => cases hx
  | finite _ _ _ => rfl

theorem sub_inf_finite (s : Bool) (y : IEEEFloat eb mb)
    (hy : y.isFinite = true) :
    sub heb hmb (.inf s) y = .inf s := by
  cases y with
  | nan => cases hy
  | inf _ => cases hy
  | finite _ _ _ => rfl

theorem sub_finite_inf (s : Bool) (x : IEEEFloat eb mb)
    (hx : x.isFinite = true) :
    sub heb hmb x (.inf s) = .inf (!s) := by
  cases x with
  | nan => cases hx
  | inf _ => cases hx
  | finite _ _ _ => rfl

theorem mul_inf_inf (sx sy : Bool) :
    mul heb hmb ((.inf sx) : IEEEFloat eb mb) (.inf sy) = .inf (sx != sy) := rfl

theorem div_inf_inf (sx sy : Bool) :
    div heb hmb ((.inf sx) : IEEEFloat eb mb) (.inf sy) = .nan := rfl

end Arithmetic

/-! ## Operation equivalences

Identities that hold *for all inputs* (NaN included), not just under
side conditions.  These come from the way `Backend` defines each
operation via rounded real arithmetic plus the symmetry of `+` / `*`
on `ℝ`.

These are the IEEE 754 invariants that *do* hold despite rounding —
catalogued for ergonomics, since downstream proofs reach for them
constantly. -/

section Equivalences
variable (heb : 1 ≤ eb) (hmb : 1 ≤ mb)

private theorem bne_comm (a b : Bool) : (a != b) = (b != a) := by
  cases a <;> cases b <;> rfl

/-- Subtraction is addition of negation, exactly. -/
theorem sub_eq_add_neg' (a b : IEEEFloat eb mb) :
    sub heb hmb a b = add heb hmb a (-b) := by
  cases a with
  | nan => cases b <;> rfl
  | inf sa =>
    cases b with
    | nan => rfl
    | inf sb => cases sa <;> cases sb <;> rfl
    | finite _ _ _ => rfl
  | finite sa ea ma =>
    cases b with
    | nan => rfl
    | inf sb => cases sb <;> rfl
    | finite sb eb_ mb_ =>
      show roundToNearestEven heb hmb (finiteValue sa ea ma - finiteValue sb eb_ mb_)
        = roundToNearestEven heb hmb (finiteValue sa ea ma + finiteValue (!sb) eb_ mb_)
      have h_neg : finiteValue (!sb) eb_ mb_ = -(finiteValue sb eb_ mb_) := by
        unfold finiteValue
        rcases sb with _ | _ <;> simp <;> split_ifs <;> ring
      rw [h_neg]
      rfl

/-- Addition commutes (the rounded sum is symmetric). -/
theorem add_comm_eq (a b : IEEEFloat eb mb) :
    add heb hmb a b = add heb hmb b a := by
  cases a with
  | nan => cases b <;> rfl
  | inf sa =>
    cases b with
    | nan => rfl
    | inf sb =>
      simp only [add]
      by_cases h : sa = sb
      · rw [if_pos h, if_pos h.symm, h]
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]
    | finite _ _ _ => rfl
  | finite sa ea ma =>
    cases b with
    | nan => rfl
    | inf _ => rfl
    | finite sb eb_ mb_ =>
      show roundToNearestEven heb hmb (finiteValue sa ea ma + finiteValue sb eb_ mb_)
        = roundToNearestEven heb hmb (finiteValue sb eb_ mb_ + finiteValue sa ea ma)
      rw [add_comm]

/-- Multiplication commutes. -/
theorem mul_comm_eq (a b : IEEEFloat eb mb) :
    mul heb hmb a b = mul heb hmb b a := by
  cases a with
  | nan => cases b <;> rfl
  | inf sa =>
    cases b with
    | nan => rfl
    | inf sb => simp only [mul]; rw [bne_comm]
    | finite sb eb_ mb_ =>
      simp only [mul]
      split_ifs with hbz
      · rfl
      · rw [bne_comm]
  | finite sa ea ma =>
    cases b with
    | nan => rfl
    | inf sb =>
      simp only [mul]
      split_ifs with haz
      · rfl
      · rw [bne_comm]
    | finite sb eb_ mb_ =>
      show roundToNearestEven heb hmb (finiteValue sa ea ma * finiteValue sb eb_ mb_)
        = roundToNearestEven heb hmb (finiteValue sb eb_ mb_ * finiteValue sa ea ma)
      rw [mul_comm]

/-! ### Equivalences with rounding involved

The previous block had exact equivalences whose RHS happens to round
to the same value.  This block has equivalences that *go through*
rounding — both sides call `roundToNearestEven` on values that are
propositionally (not definitionally) equal, then a `congr 1`
collapses them. -/

/-- `fma a b z = mul a b` when `z` is any zero (regardless of sign).
    Both sides round once over the same real product `a * b`; the
    `+0` term in fma vanishes via `add_zero`. -/
theorem fma_zero_third_eq_mul (a b z : IEEEFloat eb mb) (hz : z.isZero = true) :
    fma heb hmb a b z = mul heb hmb a b := by
  cases z with
  | nan => cases hz
  | inf _ => cases hz
  | finite sz ez mz =>
    have h_z_val : finiteValue sz ez mz = 0 := by
      simp [isZero] at hz
      unfold finiteValue
      rcases sz <;> simp [hz.1, hz.2]
    cases a with
    | nan => rfl
    | inf sa =>
      cases b with
      | nan => rfl
      | inf sb => rfl
      | finite sb eb_ mb_ => rfl
    | finite sa ea ma =>
      cases b with
      | nan => rfl
      | inf sb => rfl
      | finite sb eb_ mb_ =>
        show roundToNearestEven heb hmb
              (finiteValue sa ea ma * finiteValue sb eb_ mb_ + finiteValue sz ez mz)
          = roundToNearestEven heb hmb
              (finiteValue sa ea ma * finiteValue sb eb_ mb_)
        rw [h_z_val, add_zero]

/-- `fma a b (-z) = mul a b` when `z` is any zero — corollary of the
    above, since `-z` is also a zero (sign flipped, value 0). -/
theorem fma_neg_zero_third_eq_mul (a b z : IEEEFloat eb mb) (hz : z.isZero = true) :
    fma heb hmb a b (-z) = mul heb hmb a b :=
  fma_zero_third_eq_mul heb hmb a b (-z) (by rw [isZero_neg]; exact hz)

/-! #### Real-value equivalences

These hold *unconditionally* at the real-value level, even when the
encoding-level equality fails (the `±0` ambiguity from `Classical.choose`
disappears once you go through `toRealOrZero`). -/

/-- For any in-range real `r`, `roundToNearestEven` is *idempotent on
    representable values* — at the real-value level.  If `x` is finite
    and represents `r` exactly, then any RNE of `r` reads back as `r`
    via `toRealOrZero` (even if the chosen encoding differs from `x`
    in the `+0` / `−0` ambiguity). -/
theorem roundToNearestEven_toRealOrZero_of_finite
    (x : IEEEFloat eb mb) (hx : x.isFinite = true)
    (hover : |x.toRealOrZero| < overflowBoundary eb mb) :
    (roundToNearestEven heb hmb x.toRealOrZero).toRealOrZero = x.toRealOrZero := by
  have h_rne := roundToNearestEven_isRNE heb hmb x.toRealOrZero
  obtain ⟨_, h_in_range⟩ := h_rne
  obtain ⟨_, h_min, _⟩ := h_in_range hover
  -- `roundToNearestEven` is at minimum distance from `x.toRealOrZero`,
  -- and `x` itself achieves zero distance, so the result must too.
  have h_x_zero : |x.toRealOrZero - x.toRealOrZero| = 0 := by simp
  have h_le := h_min x hx
  rw [h_x_zero] at h_le
  have h_eq : |(roundToNearestEven heb hmb x.toRealOrZero).toRealOrZero
              - x.toRealOrZero| = 0 :=
    le_antisymm h_le (abs_nonneg _)
  have := abs_eq_zero.mp h_eq
  linarith

end Equivalences

end IEEEFloat
