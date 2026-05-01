import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Round
import IEEEFloat.RoundExistence

/-! # Integer ↔ floating-point conversions (IEEE 754 §5.4.1)

  *  `convertFromInt : ℤ → IEEEFloat` — RNE rounding of an integer
     to the format.  Always defined; large integers may overflow to
     ±∞ via `roundToNearestEven`'s overflow rule.
  *  `truncToInt` (toward zero), `floorToInt` (toward −∞),
     `ceilToInt` (toward +∞) — the three deterministic
     `convertToInteger` modes.
  *  `roundToIntTiesAway`, `roundToIntTiesEven` — the two
     ties-broken `convertToInteger` modes.

NaN and ±∞ inputs to `convertToInteger*` yield `0` (a sentinel).
IEEE 754 specifies "raise invalid" — but this library is purely
functional and doesn't model floating-point exception flags, so the
caller is responsible for excluding NaN/Inf inputs at a higher level.

The two ties-broken variants are defined directly via `Int.floor`
on a shifted argument; their `tiesEven` form implements banker's
rounding (Python `round`, IEEE 754 default for integer rounding).
-/

namespace IEEEFloat

variable {eb mb : Nat}

/-! ## Integer → float -/

/-- Convert an integer to a floating-point value via round-to-nearest-even.
    Out-of-range integers (those whose magnitude exceeds the format's
    `overflowBoundary`) round to ±∞. -/
noncomputable def convertFromInt (heb : 1 ≤ eb) (hmb : 1 ≤ mb)
    (n : ℤ) : IEEEFloat eb mb :=
  roundToNearestEven heb hmb (n : ℝ)

/-- The result of `convertFromInt` satisfies the RNE predicate against
    the integer's real value. -/
theorem convertFromInt_isRNE (heb : 1 ≤ eb) (hmb : 1 ≤ mb) (n : ℤ) :
    IsRoundedToNearestEven (n : ℝ)
      (convertFromInt (eb := eb) (mb := mb) heb hmb n) :=
  roundToNearestEven_isRNE heb hmb _

/-! ## Float → integer

NaN and ±∞ inputs return `0` as a sentinel; downstream code should
guard with `isFinite` if it cares.  For finite inputs, each variant
applies the named rounding rule to the real value. -/

/-- Truncation toward zero (`(int)x` in C). -/
noncomputable def truncToInt : IEEEFloat eb mb → ℤ
  | .nan => 0
  | .inf _ => 0
  | .finite s e m =>
      let r : ℝ := finiteValue s e m
      if 0 ≤ r then ⌊r⌋ else ⌈r⌉

/-- Floor: round toward −∞. -/
noncomputable def floorToInt : IEEEFloat eb mb → ℤ
  | .nan => 0
  | .inf _ => 0
  | .finite s e m => ⌊(finiteValue s e m : ℝ)⌋

/-- Ceiling: round toward +∞. -/
noncomputable def ceilToInt : IEEEFloat eb mb → ℤ
  | .nan => 0
  | .inf _ => 0
  | .finite s e m => ⌈(finiteValue s e m : ℝ)⌉

/-- Round to nearest, ties away from zero (e.g., C `lround`). -/
noncomputable def roundToIntTiesAway : IEEEFloat eb mb → ℤ
  | .nan => 0
  | .inf _ => 0
  | .finite s e m =>
      let r : ℝ := finiteValue s e m
      if 0 ≤ r then ⌊r + 1/2⌋ else -⌊-r + 1/2⌋

/-- Round to nearest, ties to even (banker's rounding; IEEE 754
    default for integer rounding). -/
noncomputable def roundToIntTiesEven : IEEEFloat eb mb → ℤ
  | .nan => 0
  | .inf _ => 0
  | .finite s e m =>
      let r : ℝ := finiteValue s e m
      let n : ℤ := ⌊r⌋
      let frac : ℝ := r - n
      if frac < 1/2 then n
      else if frac > 1/2 then n + 1
      else if n % 2 = 0 then n else n + 1

/-! ## Sanity theorems -/

@[simp] theorem truncToInt_nan :
    truncToInt (.nan : IEEEFloat eb mb) = 0 := rfl
@[simp] theorem truncToInt_inf (s : Bool) :
    truncToInt ((.inf s) : IEEEFloat eb mb) = 0 := rfl

@[simp] theorem floorToInt_nan :
    floorToInt (.nan : IEEEFloat eb mb) = 0 := rfl
@[simp] theorem floorToInt_inf (s : Bool) :
    floorToInt ((.inf s) : IEEEFloat eb mb) = 0 := rfl

@[simp] theorem ceilToInt_nan :
    ceilToInt (.nan : IEEEFloat eb mb) = 0 := rfl
@[simp] theorem ceilToInt_inf (s : Bool) :
    ceilToInt ((.inf s) : IEEEFloat eb mb) = 0 := rfl

@[simp] theorem roundToIntTiesAway_nan :
    roundToIntTiesAway (.nan : IEEEFloat eb mb) = 0 := rfl
@[simp] theorem roundToIntTiesAway_inf (s : Bool) :
    roundToIntTiesAway ((.inf s) : IEEEFloat eb mb) = 0 := rfl

@[simp] theorem roundToIntTiesEven_nan :
    roundToIntTiesEven (.nan : IEEEFloat eb mb) = 0 := rfl
@[simp] theorem roundToIntTiesEven_inf (s : Bool) :
    roundToIntTiesEven ((.inf s) : IEEEFloat eb mb) = 0 := rfl

/-- Floor agrees with `Int.floor` of the real value. -/
theorem floorToInt_finite (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    floorToInt (.finite s e m : IEEEFloat eb mb)
      = ⌊(finiteValue s e m : ℝ)⌋ := rfl

/-- Ceiling agrees with `Int.ceil` of the real value. -/
theorem ceilToInt_finite (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    ceilToInt (.finite s e m : IEEEFloat eb mb)
      = ⌈(finiteValue s e m : ℝ)⌉ := rfl

end IEEEFloat
