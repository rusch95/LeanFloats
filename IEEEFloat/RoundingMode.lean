import IEEEFloat.Round

/-! # Rounding-mode framework (IEEE 754 §4.3)

IEEE 754-2019 §4.3 specifies five rounding-direction attributes:

  | abbreviation | name                       | rule                                 |
  |--------------|----------------------------|--------------------------------------|
  | RNE          | roundTiesToEven            | nearest, ties to even mantissa LSB   |
  | RNA          | roundTiesToAway            | nearest, ties away from zero         |
  | RTZ          | roundTowardZero            | truncation toward zero               |
  | RTP          | roundTowardPositive        | ceiling (toward +∞)                  |
  | RTN          | roundTowardNegative        | floor (toward −∞)                    |

This module sets up the framework: the `RoundingMode` enum and the
unified `IsRoundedTo` predicate.  The rest of the library
(`Round.lean`, `RoundExistence.lean`, `Backend.lean`) currently
specialises to RNE — IEEE's default — which suffices for almost all
correctness obligations.

The four non-RNE modes are *specified* here but not yet proved to
have constructive witnesses.  Adding `roundTowardZero` etc. as
named functions follows the same `Finset.exists_min_image` /
`Classical.choose` recipe used in `RoundExistence.lean` for RNE,
but with different argmin / argmax criteria.

## Overflow rules

IEEE 754 §4.3.1 distinguishes the modes' overflow handling:

  *  **RNE / RNA:** overflow rounds to ±∞ with the sign of `r`.
  *  **RTZ:** overflow rounds to ±`maxFinite` (toward zero — never
     produces infinity for a finite-magnitude real input).
  *  **RTP:** positive overflow → +∞; negative overflow → −maxFinite.
  *  **RTN:** positive overflow → +maxFinite; negative overflow → −∞.

These are encoded directly in the per-mode predicate definitions.
-/

namespace IEEEFloat

variable {eb mb : Nat}

/-- The five IEEE 754-2019 rounding-direction attributes. -/
inductive RoundingMode
  | tiesToEven
  | tiesToAway
  | towardZero
  | towardPositive
  | towardNegative
  deriving DecidableEq, Repr

/-! ## `IsRoundedTo` — the unified predicate

For RNE we reuse the existing `IsRoundedToNearestEven`.  For the
other four modes we spell out the spec inline, since they use
different overflow rules and different tie-break rules. -/

/-- `IsRoundedToward r z` (toward zero / RTZ): for in-range `r`, `z`
    is finite, has `|z.toRealOrZero| ≤ |r|`, and is the *largest*
    such (closest to `r` from the inside).  For overflow, `z` is
    `±maxFinite` with the sign of `r`. -/
def IsRoundedTowardZero (r : ℝ) (x : IEEEFloat eb mb) : Prop :=
  -- Positive overflow: x = +maxFinite (largest positive)
  (overflowBoundary eb mb ≤ r →
    ∃ (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)),
      x = .finite false e m ∧
      e.val = 2 ^ eb - 1 - 1 ∧ m.val = 2 ^ mb - 1) ∧
  -- Negative overflow: x = -maxFinite
  (r ≤ -overflowBoundary eb mb →
    ∃ (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)),
      x = .finite true e m ∧
      e.val = 2 ^ eb - 1 - 1 ∧ m.val = 2 ^ mb - 1) ∧
  -- In-range: z is the closest finite with |z| ≤ |r|
  (|r| < overflowBoundary eb mb →
    x.isFinite = true ∧
    |x.toRealOrZero| ≤ |r| ∧
    (∀ y : IEEEFloat eb mb, y.isFinite = true →
       |y.toRealOrZero| ≤ |r| →
       |y.toRealOrZero| ≤ |x.toRealOrZero|))

/-- `IsRoundedTowardPositive r z` (RTP / ceiling): `z` is the
    smallest finite value with `z ≥ r`.  Overflow: positive
    overflow → `+∞`; negative overflow → `−maxFinite`. -/
def IsRoundedTowardPositive (r : ℝ) (x : IEEEFloat eb mb) : Prop :=
  (overflowBoundary eb mb ≤ r → x = .inf false) ∧
  (r ≤ -overflowBoundary eb mb →
    ∃ (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)),
      x = .finite true e m ∧
      e.val = 2 ^ eb - 1 - 1 ∧ m.val = 2 ^ mb - 1) ∧
  (|r| < overflowBoundary eb mb →
    x.isFinite = true ∧
    r ≤ x.toRealOrZero ∧
    (∀ y : IEEEFloat eb mb, y.isFinite = true →
       r ≤ y.toRealOrZero →
       x.toRealOrZero ≤ y.toRealOrZero))

/-- `IsRoundedTowardNegative r z` (RTN / floor): `z` is the largest
    finite value with `z ≤ r`.  Overflow: positive overflow →
    `+maxFinite`; negative overflow → `−∞`. -/
def IsRoundedTowardNegative (r : ℝ) (x : IEEEFloat eb mb) : Prop :=
  (overflowBoundary eb mb ≤ r →
    ∃ (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)),
      x = .finite false e m ∧
      e.val = 2 ^ eb - 1 - 1 ∧ m.val = 2 ^ mb - 1) ∧
  (r ≤ -overflowBoundary eb mb → x = .inf true) ∧
  (|r| < overflowBoundary eb mb →
    x.isFinite = true ∧
    x.toRealOrZero ≤ r ∧
    (∀ y : IEEEFloat eb mb, y.isFinite = true →
       y.toRealOrZero ≤ r →
       y.toRealOrZero ≤ x.toRealOrZero))

/-- `IsRoundedTiesToAway r z` (RNA): nearest, ties broken away from
    zero.  Used by C `lround` / `llround` / `lrint` family.
    Overflow same as RNE (±∞ with the sign of `r`). -/
def IsRoundedTiesToAway (r : ℝ) (x : IEEEFloat eb mb) : Prop :=
  (overflowBoundary eb mb ≤ |r| →
      (0 ≤ r → x = .inf false) ∧ (r < 0 → x = .inf true)) ∧
  (|r| < overflowBoundary eb mb →
      x.isFinite = true ∧
      (∀ y : IEEEFloat eb mb, y.isFinite = true →
        |x.toRealOrZero - r| ≤ |y.toRealOrZero - r|) ∧
      (∀ y : IEEEFloat eb mb, y.isFinite = true → y ≠ x →
        |x.toRealOrZero - r| = |y.toRealOrZero - r| →
        |r| ≤ |x.toRealOrZero|))

/-- The unified rounding predicate, parameterised by a `RoundingMode`. -/
def IsRoundedTo (mode : RoundingMode) (r : ℝ) (x : IEEEFloat eb mb) : Prop :=
  match mode with
  | .tiesToEven      => IsRoundedToNearestEven r x
  | .tiesToAway      => IsRoundedTiesToAway r x
  | .towardZero      => IsRoundedTowardZero r x
  | .towardPositive  => IsRoundedTowardPositive r x
  | .towardNegative  => IsRoundedTowardNegative r x

/-- Sanity: `IsRoundedTo .tiesToEven` reduces to the existing predicate. -/
@[simp] theorem IsRoundedTo_tiesToEven (r : ℝ) (x : IEEEFloat eb mb) :
    IsRoundedTo .tiesToEven r x ↔ IsRoundedToNearestEven r x := Iff.rfl

@[simp] theorem IsRoundedTo_tiesToAway (r : ℝ) (x : IEEEFloat eb mb) :
    IsRoundedTo .tiesToAway r x ↔ IsRoundedTiesToAway r x := Iff.rfl

@[simp] theorem IsRoundedTo_towardZero (r : ℝ) (x : IEEEFloat eb mb) :
    IsRoundedTo .towardZero r x ↔ IsRoundedTowardZero r x := Iff.rfl

@[simp] theorem IsRoundedTo_towardPositive (r : ℝ) (x : IEEEFloat eb mb) :
    IsRoundedTo .towardPositive r x ↔ IsRoundedTowardPositive r x := Iff.rfl

@[simp] theorem IsRoundedTo_towardNegative (r : ℝ) (x : IEEEFloat eb mb) :
    IsRoundedTo .towardNegative r x ↔ IsRoundedTowardNegative r x := Iff.rfl

/-! ## Status

Existence theorems for the non-RNE modes (analogous to `rne_exists`
in `IEEEFloat.RoundExistence`) are *not* proved here.  Each follows
the same template — `Finset.exists_min_image` / `exists_max_image`
on the finite set of finite encodings against a per-mode criterion
— but each requires its own invariant lemmas and tie-break-witness
construction.  When a downstream consumer needs a non-RNE
constructive `roundTo` function, the proof can be added by
analogy.
-/

end IEEEFloat
