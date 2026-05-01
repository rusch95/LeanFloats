import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import IEEEFloat.Real

/-! # Standard floating-point operations beyond ±×÷

This module collects the IEEE 754 §5.5 (quiet-computational) and
§5.7 (non-computational) operations that are *not* themselves rounded:

  *  `abs` — clear sign bit (§5.5.1).
  *  `copySign` — copy the sign of one operand onto another (§5.5.1).
  *  `fpclass` — unified class predicate (§5.7.2), distinguishing
     all ten classes of IEEE 754 values.

All three are total, computable, constructor-level — no `ℝ`
arithmetic, no rounding.  `IEEEFloat.Compare` adds the comparison
operations (`lt`/`le`/`eq`/`unordered`) and `minimum`/`maximum`,
which build on these primitives.
-/

namespace IEEEFloat

variable {eb mb : Nat}

/-! ## `abs` -/

/-- Absolute value: clear the sign bit.  `abs .nan = .nan` (since
    our `.nan` already erases sign). -/
def abs : IEEEFloat eb mb → IEEEFloat eb mb
  | .nan          => .nan
  | .inf _        => .inf false
  | .finite _ e m => .finite false e m

@[simp] theorem abs_nan : abs (.nan : IEEEFloat eb mb) = .nan := rfl
@[simp] theorem abs_inf (s : Bool) :
    abs ((.inf s) : IEEEFloat eb mb) = .inf false := rfl
@[simp] theorem abs_finite (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    abs (.finite s e m) = .finite false e m := rfl

/-- `abs` is idempotent. -/
theorem abs_abs (x : IEEEFloat eb mb) : abs (abs x) = abs x := by
  cases x <;> rfl

/-- `abs` clears the sign bit. -/
theorem signBit_abs (x : IEEEFloat eb mb) : (abs x).signBit = false := by
  cases x <;> rfl

/-- `abs` and IEEEFloat negation: `abs (-x) = abs x`. -/
theorem abs_neg_eq (x : IEEEFloat eb mb) : abs (-x) = abs x := by
  cases x <;> rfl

/-- Helper: every `finiteValue` reading is `≥ 0` when sign is `false`. -/
private theorem finiteValue_pos_nonneg
    (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    (0 : ℝ) ≤ finiteValue false e m := by
  unfold finiteValue
  simp
  split_ifs with h_e
  · exact mul_nonneg (le_of_lt (zpow_pos (by norm_num) _)) (by positivity)
  · exact mul_nonneg (le_of_lt (zpow_pos (by norm_num) _)) (by positivity)

/-- The negative-sign reading of a `finite` is the negation of the
    positive-sign reading. -/
private theorem finiteValue_neg_eq
    (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    finiteValue true e m = -(finiteValue false e m) := by
  unfold finiteValue; simp; split_ifs <;> ring

/-- For finite `x`, `abs` agrees with the real-valued absolute
    value of `toRealOrZero`. -/
theorem abs_toRealOrZero_eq (x : IEEEFloat eb mb) (hx : x.isFinite = true) :
    (abs x).toRealOrZero = |x.toRealOrZero| := by
  cases x with
  | nan => cases hx
  | inf _ => cases hx
  | finite s e m =>
    show (finiteValue false e m : ℝ) = |finiteValue s e m|
    rcases s with _ | _
    · exact (abs_of_nonneg (finiteValue_pos_nonneg e m)).symm
    · rw [finiteValue_neg_eq, abs_neg]
      exact (abs_of_nonneg (finiteValue_pos_nonneg e m)).symm

/-! ## `copySign`

`copySign x y` produces a value with the magnitude of `x` and the
sign of `y`.  IEEE 754 §5.5.1: this is a *quiet* operation — no
exceptions — and operates on quiet NaN by preserving the NaN
encoding (with the new sign).  Since our `.nan` already erases
sign, we return `.nan` for any NaN-`x` input. -/

/-- Copy the sign bit of `y` onto `x`. -/
def copySign : IEEEFloat eb mb → IEEEFloat eb mb → IEEEFloat eb mb
  | .nan, _          => .nan
  | .inf _, y        => .inf y.signBit
  | .finite _ e m, y => .finite y.signBit e m

@[simp] theorem copySign_nan (y : IEEEFloat eb mb) :
    copySign .nan y = .nan := rfl
@[simp] theorem copySign_inf (s : Bool) (y : IEEEFloat eb mb) :
    copySign (.inf s) y = .inf y.signBit := rfl
@[simp] theorem copySign_finite (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb))
    (y : IEEEFloat eb mb) :
    copySign (.finite s e m) y = .finite y.signBit e m := rfl

/-- The sign of `copySign x y` matches `y` (for non-NaN `x`). -/
theorem signBit_copySign (x y : IEEEFloat eb mb) (hx : x ≠ .nan) :
    (copySign x y).signBit = y.signBit := by
  cases x with
  | nan => exact absurd rfl hx
  | inf _ => rfl
  | finite _ _ _ => rfl

/-- `copySign` ignores the sign of its first argument. -/
theorem copySign_abs_left (x y : IEEEFloat eb mb) :
    copySign (abs x) y = copySign x y := by
  cases x <;> rfl

/-- `copySign x x = x`: copying a value's own sign is a no-op. -/
theorem copySign_self (x : IEEEFloat eb mb) : copySign x x = x := by
  cases x with
  | nan => rfl
  | inf s => rfl
  | finite s e m => rfl

/-! ## `FloatClass` and `fpclass`

IEEE 754 §5.7.2's `class` operation discriminates a float into one
of ten classes.  We collapse `signalingNaN` into `quietNaN` here
(consistent with the rest of the library — we don't model
signaling NaNs). -/

/-- IEEE 754 §5.7.2 floating-point classes.  We collapse signaling
    and quiet NaNs into a single `qNaN` constructor, since this
    library does not model signaling NaNs. -/
inductive FloatClass
  | qNaN
  | negInf
  | negNormal
  | negSubnormal
  | negZero
  | posZero
  | posSubnormal
  | posNormal
  | posInf
  deriving DecidableEq, Repr

/-- IEEE 754 §5.7.2 `class` operation: classify a float. -/
def fpclass : IEEEFloat eb mb → FloatClass
  | .nan          => .qNaN
  | .inf false    => .posInf
  | .inf true     => .negInf
  | .finite s e m =>
      if e.val = 0 ∧ m.val = 0 then
        if s then .negZero else .posZero
      else if e.val = 0 then
        if s then .negSubnormal else .posSubnormal
      else
        if s then .negNormal else .posNormal

@[simp] theorem fpclass_nan :
    fpclass (.nan : IEEEFloat eb mb) = .qNaN := rfl
@[simp] theorem fpclass_posInf :
    fpclass ((.inf false) : IEEEFloat eb mb) = .posInf := rfl
@[simp] theorem fpclass_negInf :
    fpclass ((.inf true) : IEEEFloat eb mb) = .negInf := rfl

/-! ### Linking `fpclass` to existing predicates

Each existing `is*` predicate corresponds to a subset of
`FloatClass` values. -/

theorem isNaN_iff (x : IEEEFloat eb mb) :
    x.isNaN = true ↔ fpclass x = .qNaN := by
  cases x with
  | nan => simp [isNaN, fpclass]
  | inf s => cases s <;> simp [isNaN, fpclass]
  | finite s e m =>
    simp only [isNaN, fpclass]
    split_ifs <;> simp

theorem isInf_iff (x : IEEEFloat eb mb) :
    x.isInf = true ↔ (fpclass x = .posInf ∨ fpclass x = .negInf) := by
  cases x with
  | nan => simp [isInf, fpclass]
  | inf s => cases s <;> simp [isInf, fpclass]
  | finite s e m =>
    simp only [isInf, fpclass]
    split_ifs <;> simp

theorem isZero_iff (x : IEEEFloat eb mb) :
    x.isZero = true ↔ (fpclass x = .posZero ∨ fpclass x = .negZero) := by
  cases x with
  | nan => simp [isZero, fpclass]
  | inf s => cases s <;> simp [isZero, fpclass]
  | finite s e m =>
    simp only [isZero, fpclass]
    rcases h_e : e.val with _ | _
    · rcases h_m : m.val with _ | _
      · rcases s <;> simp
      · rcases s <;> simp
    · rcases h_m : m.val with _ | _
      · rcases s <;> simp
      · rcases s <;> simp

theorem isFinite_iff (x : IEEEFloat eb mb) :
    x.isFinite = true ↔ fpclass x ≠ .qNaN ∧
                        fpclass x ≠ .posInf ∧
                        fpclass x ≠ .negInf := by
  cases x with
  | nan => simp [isFinite, fpclass]
  | inf s => cases s <;> simp [isFinite, fpclass]
  | finite s e m =>
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    simp only [fpclass]
    split_ifs <;> rcases s <;> simp

end IEEEFloat
