import Mathlib.Data.Real.Basic
import IEEEFloat.Real

/-! # Rounding — IEEE 754 §4.3 specification

This module captures **what it means** for an `IEEEFloat eb mb` to
be the correctly-rounded result of a real-valued computation,
*specifically under the default rounding mode roundTiesToEven*
(IEEE 754 §4.3.1).  No constructive `roundToNearestEven : ℝ → F`
function is provided here — that lands in a follow-up commit and is
where the heavy proof work lives (existence + uniqueness modulo
±0 / RNE tie-breaking).

The spec form is sufficient to:

  *  state correctness for arithmetic operations
     (`a + b` is RNE of `a.toReal + b.toReal`),
  *  derive a 1-ulp relative-error bound on rounded operations
     (the `Sterbenz`/`relative_error_le_ulp` family of lemmas).

Tie-breaking is encoded by quantifying over all equidistant finite
neighbours: when `x` is RNE of `r`, any *other* finite encoding `y`
at the same distance from `r` exists only if `x`'s mantissa LSB is
zero (even-mantissa rule).
-/

namespace IEEEFloat

variable {eb mb : Nat}

/-! ## Format-specific real-valued boundaries -/

/-- Largest finite value: `(2 - 2^{-mb}) · 2^{maxExp}`.
    f32 → ≈ 3.4 × 10³⁸. -/
noncomputable def maxFinite (eb mb : Nat) : ℝ :=
  ((2 : ℝ) - (2 : ℝ) ^ (-(mb : Int))) * (2 : ℝ) ^ maxExp eb

/-- Smallest positive subnormal: `2^{minSubnormalExp}`.
    f32 → 2⁻¹⁴⁹ ≈ 1.4 × 10⁻⁴⁵. -/
noncomputable def minPosSubnormal (eb mb : Nat) : ℝ :=
  (2 : ℝ) ^ minSubnormalExp eb mb

/-- ULP at the top of the finite range: `2^{maxExp - mb}`.  Used as
    half the rounding-overflow ball, per IEEE 754 §4.3.1. -/
noncomputable def topUlp (eb mb : Nat) : ℝ :=
  (2 : ℝ) ^ (maxExp eb - mb)

/-- Magnitude past which RNE produces ±∞ (the open boundary):
    `maxFinite + topUlp / 2`.  Anything strictly below this still
    rounds to a finite value; anything at-or-above rounds to ±∞. -/
noncomputable def overflowBoundary (eb mb : Nat) : ℝ :=
  maxFinite eb mb + topUlp eb mb / 2

/-! ## Spec: roundTiesToEven (RNE)

    The IEEE 754-2019 §4.3.1 default rounding direction.

    Note on the tie-break clause: it states the contrapositive form
    "if a *different* finite encoding ties with `x`, then `x` has
    mantissa LSB = 0".  This avoids the trivial `y = x` instantiation
    which would otherwise force every rounded value to have even
    mantissa.  Together with the `nearest` clause it pins down `x`
    up to the encoding-level distinction between `+0` and `−0` (both
    of which have mantissa = 0 and thus pass the even check). -/

/-- The IEEE 754 default rounding direction `roundTiesToEven`. -/
def IsRoundedToNearestEven (r : ℝ) (x : IEEEFloat eb mb) : Prop :=
  -- Overflow regime: input magnitude at-or-past the rounding-overflow
  -- boundary rounds to ±∞ with the sign of `r`.
  (overflowBoundary eb mb ≤ |r| →
      (0 ≤ r → x = .inf false) ∧ (r < 0 → x = .inf true)) ∧
  -- In-range regime: result is finite, nearest, ties broken to even.
  (|r| < overflowBoundary eb mb →
      x.isFinite = true ∧
      (∀ y : IEEEFloat eb mb, y.isFinite = true →
        |x.toRealOrZero - r| ≤ |y.toRealOrZero - r|) ∧
      (∀ y : IEEEFloat eb mb, y.isFinite = true → y ≠ x →
        |x.toRealOrZero - r| = |y.toRealOrZero - r| →
        ∃ (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)),
          x = .finite s e m ∧ m.val % 2 = 0))

/-! ## Round-to-nearest (without tie-break)

    `IsRoundedToNearest` is the strict-RNE predicate with the
    even-mantissa tie-break clause dropped.  Any RN result that
    happens to be uniquely closest to the input also satisfies RNE
    (vacuously, since the tie-break is over `y ≠ x` with
    `|x - r| = |y - r|`); the difference between the two predicates
    therefore lives entirely in the midpoint case.

    `IsRoundedToNearest` admits a clean classical-existence proof
    via `Finset.exists_min_image` over the finite set of finite
    encodings (see `IEEEFloat.RoundExistence`).  The strengthening
    to `IsRoundedToNearestEven` requires a structural fact about the
    representable real values — adjacent representables alternate in
    mantissa-LSB parity, so any midpoint tie comes with at least one
    even-mantissa candidate — which is its own follow-up commit. -/

/-- Round-to-nearest (no tie-break).  `x` is one of the (possibly
    multiple) finite encodings closest to `r`, with overflow handled
    as in `IsRoundedToNearestEven`. -/
def IsRoundedToNearest (r : ℝ) (x : IEEEFloat eb mb) : Prop :=
  (overflowBoundary eb mb ≤ |r| →
      (0 ≤ r → x = .inf false) ∧ (r < 0 → x = .inf true)) ∧
  (|r| < overflowBoundary eb mb →
      x.isFinite = true ∧
      (∀ y : IEEEFloat eb mb, y.isFinite = true →
        |x.toRealOrZero - r| ≤ |y.toRealOrZero - r|))

/-- RNE strengthens RN: dropping the tie-break clause. -/
theorem IsRoundedToNearest.of_rne {r : ℝ} {x : IEEEFloat eb mb}
    (h : IsRoundedToNearestEven r x) : IsRoundedToNearest r x :=
  ⟨h.1, fun hr => ⟨(h.2 hr).1, (h.2 hr).2.1⟩⟩

/-! ## RNE existence (deferred)

    `IsRoundedToNearestEven` existence is the next-commit obligation.
    Downstream modules that need the full RNE contract may, until
    then, assume an `IsRoundedToNearestEven r x` witness in the
    same `[FloatSpec F]`-style as the WGSL repo. -/

end IEEEFloat
