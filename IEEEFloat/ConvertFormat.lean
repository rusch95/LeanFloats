import IEEEFloat.RoundExistence

/-! # Cross-format conversion (IEEE 754 §5.4.2)

`convertFormat : IEEEFloat eb1 mb1 → IEEEFloat eb2 mb2` rounds an
IEEEFloat in one binary interchange format to another.  The single
function handles all four common transitions:

  *  Widening (f32 → f64, bf16 → f32): rounding is *exact* for any
     value representable in the source format, since every source
     value is representable in the target.
  *  Narrowing (f64 → f32, f32 → bf16): RNE applies, with the
     usual overflow-to-±∞ behaviour at the target's
     `overflowBoundary`.
  *  Same format (`eb1 = eb2`, `mb1 = mb2`): exact identity on
     finite encodings (modulo `+0`/`−0` distinction, which is
     preserved).

NaN and ±∞ pass through unchanged (modulo our canonical NaN —
`.nan` always maps to `.nan`).

For the same reason as `Backend`, the function is `noncomputable`
(it goes through `roundToNearestEven`) — but every special case
matches exactly and downstream consumers can pattern-match.
-/

namespace IEEEFloat

variable {eb1 mb1 eb2 mb2 : Nat}

/-- Convert between two IEEE binary interchange formats.  Finite
    values are rounded to the target via `roundToNearestEven`;
    NaN and ±∞ pass through. -/
noncomputable def convertFormat (heb : 1 ≤ eb2) (hmb : 1 ≤ mb2)
    (a : IEEEFloat eb1 mb1) : IEEEFloat eb2 mb2 :=
  match a with
  | .nan          => .nan
  | .inf s        => .inf s
  | .finite s e m => roundToNearestEven heb hmb (finiteValue s e m)

/-! ## Sanity theorems -/

@[simp] theorem convertFormat_nan (heb : 1 ≤ eb2) (hmb : 1 ≤ mb2) :
    convertFormat (eb1 := eb1) (mb1 := mb1) heb hmb .nan = .nan := rfl

@[simp] theorem convertFormat_inf (heb : 1 ≤ eb2) (hmb : 1 ≤ mb2) (s : Bool) :
    convertFormat (eb1 := eb1) (mb1 := mb1) heb hmb (.inf s) = .inf s := rfl

theorem convertFormat_finite_isRNE
    (heb : 1 ≤ eb2) (hmb : 1 ≤ mb2)
    (s : Bool) (e : Fin (2 ^ eb1 - 1)) (m : Fin (2 ^ mb1)) :
    IsRoundedToNearestEven (finiteValue s e m)
      (convertFormat (eb1 := eb1) (mb1 := mb1) (eb2 := eb2) (mb2 := mb2)
        heb hmb (.finite s e m)) :=
  roundToNearestEven_isRNE heb hmb _

/-- For any finite source `a`, the converted value is the RNE of
    `a`'s real value in the target format. -/
theorem convertFormat_isRNE (heb : 1 ≤ eb2) (hmb : 1 ≤ mb2)
    (a : IEEEFloat eb1 mb1) (ra : ℝ) (hra : a.toReal = some ra) :
    IsRoundedToNearestEven ra (convertFormat heb hmb a) := by
  cases a with
  | nan => simp [toReal] at hra
  | inf _ => simp [toReal] at hra
  | finite s e m =>
    simp [toReal] at hra
    subst hra
    exact convertFormat_finite_isRNE heb hmb s e m

end IEEEFloat
