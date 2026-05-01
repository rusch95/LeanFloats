import MX.Ops
import MX.E8M0

/-! # Comparison and min/max for MX

Mirrors `IEEEFloat.Compare` for E2M1 and E8M0.  Two notable
simplifications relative to IEEE 754:

  *  **E2M1 has no NaN, no Inf.**  Every element pair is ordered.
     The only IEEE-style nuance that survives is `+0 = −0`: the
     two signed-zero patterns compare equal under `eq` and `le`.

  *  **E8M0 has NaN but no Inf, and no signed zero** (it's a pure
     exponent format).  Comparison treats NaN as unordered with
     everything (including itself), per IEEE 754 §5.6.

`min` / `max` follow IEEE 754-2019 §5.3.1.  For E2M1 there's only
one flavour (no NaN to propagate or skip).  For E8M0 we provide
both `minimum` (NaN-propagating) and `minimumNumber` (NaN-skipping),
matching IEEE 754-2019.
-/

namespace MX

namespace E2M1

/-- Encoding-level magnitude of an E2M1: `e * 2 + m`.  Lex-comparing
    `(e, m)` agrees with magnitude order across both subnormal
    (`e = 0`) and normal (`e ≥ 1`) regimes. -/
def magNat (x : E2M1) : Nat := x.e.val * 2 + x.m.val

@[simp] theorem magNat_def (x : E2M1) : magNat x = x.e.val * 2 + x.m.val := rfl

/-! ## Comparison predicates

E2M1 has no NaN and no Inf — every value is finite — so comparison is
total.  The only nuance is `+0 = −0`. -/

/-- Less-than for E2M1.  Treats `+0` and `−0` as equal. -/
def lt (x y : E2M1) : Bool :=
  let xMag := magNat x
  let yMag := magNat y
  if xMag = 0 ∧ yMag = 0 then
    false
  else
    match x.s, y.s with
    | false, false => xMag < yMag
    | true,  true  => yMag < xMag
    | false, true  => false
    | true,  false => true

/-- Equality for E2M1.  `+0 = −0` is `true`. -/
def eq (x y : E2M1) : Bool :=
  let xMag := magNat x
  let yMag := magNat y
  if xMag = 0 ∧ yMag = 0 then
    true
  else
    decide (x.s = y.s ∧ xMag = yMag)

/-- Less-than-or-equal for E2M1: `lt x y ∨ eq x y`. -/
def le (x y : E2M1) : Bool := lt x y || eq x y

@[simp] theorem eq_self (x : E2M1) : eq x x = true := by
  unfold eq
  by_cases h : magNat x = 0
  · simp
  · simp_all

theorem le_refl (x : E2M1) : le x x = true := by
  unfold le; simp

/-! ## Min and max

No NaN at the element level, so a single flavour suffices. -/

/-- Minimum.  Returns `x` when `x ≤ y`, else `y`. -/
def min (x y : E2M1) : E2M1 := if le x y then x else y

/-- Maximum.  Returns `y` when `x ≤ y`, else `x`. -/
def max (x y : E2M1) : E2M1 := if le x y then y else x

theorem min_self (x : E2M1) : min x x = x := by unfold min; simp [le_refl]

theorem max_self (x : E2M1) : max x x = x := by unfold max; simp [le_refl]

end E2M1

namespace E8M0

/-! ## Comparison for E8M0

E8M0 has NaN but no Inf and no sign — comparisons treat NaN as
unordered (returning `false` for `lt`, `le`, `eq`).  Non-NaN
comparisons are by raw value (which corresponds directly to scale
magnitude since the format is positive-only and monotone in raw). -/

/-- Less-than for E8M0.  NaN-aware: returns `false` if either is NaN. -/
def lt (a b : E8M0) : Bool :=
  !a.isNaN && !b.isNaN && decide (a.raw.val < b.raw.val)

/-- Equality for E8M0.  Returns `false` if either operand is NaN. -/
def eq (a b : E8M0) : Bool :=
  !a.isNaN && !b.isNaN && decide (a.raw = b.raw)

/-- Less-than-or-equal: `lt ∨ eq`. -/
def le (a b : E8M0) : Bool := lt a b || eq a b

/-- Unordered: at least one operand is NaN. -/
def unordered (a b : E8M0) : Bool := a.isNaN || b.isNaN

@[simp] theorem lt_nan_left (b : E8M0) (h : nan.isNaN = true) : lt nan b = false := by
  unfold lt; simp [h]

@[simp] theorem eq_nan_left (b : E8M0) : eq nan b = false := by
  unfold eq; simp [isNaN_nan]

theorem eq_self_iff_not_nan (a : E8M0) : eq a a = !a.isNaN := by
  unfold eq
  rcases h : a.isNaN with _ | _ <;> simp

/-! ## Min / max for E8M0

Two flavours per IEEE 754-2019 §5.3.1:

  *  `minimum` / `maximum` — NaN-propagating.
  *  `minimumNumber` / `maximumNumber` — NaN-skipping. -/

/-- NaN-propagating minimum: `nan` if either operand is NaN, else
    pointwise smaller. -/
def minimum (a b : E8M0) : E8M0 :=
  if a.isNaN ∨ b.isNaN then nan
  else if a.raw.val ≤ b.raw.val then a else b

/-- NaN-propagating maximum. -/
def maximum (a b : E8M0) : E8M0 :=
  if a.isNaN ∨ b.isNaN then nan
  else if a.raw.val ≤ b.raw.val then b else a

/-- NaN-skipping minimum.  Drops a NaN operand in favour of the other;
    only both-NaN produces NaN. -/
def minimumNumber (a b : E8M0) : E8M0 :=
  match a.isNaN, b.isNaN with
  | true,  true  => nan
  | true,  false => b
  | false, true  => a
  | false, false => if a.raw.val ≤ b.raw.val then a else b

/-- NaN-skipping maximum. -/
def maximumNumber (a b : E8M0) : E8M0 :=
  match a.isNaN, b.isNaN with
  | true,  true  => nan
  | true,  false => b
  | false, true  => a
  | false, false => if a.raw.val ≤ b.raw.val then b else a

@[simp] theorem minimum_nan_left (b : E8M0) : minimum nan b = nan := by
  unfold minimum; simp [isNaN_nan]

@[simp] theorem minimum_nan_right (a : E8M0) : minimum a nan = nan := by
  unfold minimum; simp [isNaN_nan]

@[simp] theorem minimumNumber_nan_left (b : E8M0) :
    minimumNumber nan b = if b.isNaN then nan else b := by
  unfold minimumNumber
  rcases h : b.isNaN with _ | _ <;> simp [isNaN_nan]

end E8M0

end MX
