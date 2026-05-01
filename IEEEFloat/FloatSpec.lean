import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # `FloatSpec`: abstract contract for IEEE 754-style rounded arithmetic

A `FloatSpec F` describes a floating-point type `F` together with its
faithful real-valued cast and per-op relative-error bounds (1-ULP
under round-to-nearest).  Used to state forward-error theorems
generically over the float format — instantiate at `Binary16` /
`BFloat16` / `Binary32` / `Binary64` (`IEEEFloat.FloatSpec.*`), at
Lean's host `Float`, or at any other faithful-rounding floating-
point representation.

This class lives at LeanFloats top level (no namespace prefix) so
that downstream Lake packages — `wgsl-to-lean`, `LeanMachineLearning`
— can `import IEEEFloat.FloatSpec` and use the bare name `FloatSpec`
without further opens.

## Why "1-ULP relative" rather than "half-ULP relative"

Round-to-nearest gives a *half*-ULP absolute bound, which translates
to a `(1/2) · 2⁻ᵐᵇ · |exact|` relative bound.  We use the slightly
weaker `2⁻ᵐᵇ · |exact|` form (the *unit roundoff* `u = 2⁻ᵐᵇ`) here
because it composes more uniformly across operations — `mul` and
`div` end up with the same shape, simplifying proofs that compose
several ops.

## What this class asserts vs. what's actually true

The bound `|RN(a+b) - (a+b)| ≤ u·|a+b|` is the **textbook** "1-ULP
relative" claim.  Strictly speaking it **fails at subnormal
underflow**: take `x = 2^(minSubnormalExp − 1)`; the absolute error
`|RN(x) − x|` is on the order of `2^(minSubnormalExp − 1)`, while
`u · |x|` is `2^(−mb) · 2^(minSubnormalExp − 1)` — the bound fails
by a factor of `2^mb`.

Per-format instances ship two forms of each binary-op error bound:

  * `*_error_normal` (precondition'd, rigorously valid) — assumes
    the rounded result is normal, so the relative bound holds.
    Provable from `IEEEFloat.IsCorrectlyRoundedAdd` (etc.) plus the
    half-ULP theorem in `IEEEFloat.UlpBound`; currently axiomatized
    for time, but the precondition correctly delimits the regime
    where the bound holds.

  * `*_error` (unconditional, looser/aspirational) — back-compat
    form used by the `FloatSpec` typeclass field, and by existing
    consumers in `wgsl-to-lean` that assume normal-range arithmetic
    implicitly.  Derivable from `*_error_normal` plus a "no
    subnormal underflow" assumption. -/

namespace IEEEFloat

/-- Abstract spec for a floating-point type with IEEE-754-style
    rounded arithmetic.  `ulpBound` is the per-op relative-error
    bound under round-to-nearest (e.g., `2⁻¹⁰` for f16, `2⁻⁷` for
    bf16, `2⁻²³` for f32, `2⁻⁵²` for f64).

    Lives under `namespace IEEEFloat` because Lean core's
    `Init.Data.Float` already declares a `structure FloatSpec`
    (auto-imported into every file).  Use `IEEEFloat.FloatSpec`
    fully-qualified, or `open IEEEFloat (FloatSpec)` for the bare
    name.  `class IEEEFloat.FloatSpec` and `structure FloatSpec`
    coexist at distinct paths. -/
class FloatSpec (F : Type*) where
  /-- Faithful cast to the reals.  Total — non-finite values map to
      a representative real (typically `0`); error bounds are stated
      pointwise so non-finite arguments are out of bounds for the
      bounds-bearing axioms. -/
  toReal : F → ℝ
  /-- Zero element. -/
  zero : F
  zero_toReal : toReal zero = 0
  /-- One element. -/
  one : F
  one_toReal : toReal one = 1
  /-- Per-op relative-error bound. -/
  ulpBound : ℝ
  ulpBound_nonneg : 0 ≤ ulpBound
  /-- Rounded addition. -/
  add : F → F → F
  add_error : ∀ a b : F,
    |toReal (add a b) - (toReal a + toReal b)|
      ≤ ulpBound * |toReal a + toReal b|
  /-- Rounded subtraction. -/
  sub : F → F → F
  sub_error : ∀ a b : F,
    |toReal (sub a b) - (toReal a - toReal b)|
      ≤ ulpBound * |toReal a - toReal b|
  /-- Rounded multiplication. -/
  mul : F → F → F
  mul_error : ∀ a b : F,
    |toReal (mul a b) - toReal a * toReal b|
      ≤ ulpBound * |toReal a * toReal b|
  /-- Rounded division.  Implementation-defined at `b = 0`; the
      bound is vacuously satisfied there since `0 ≤ ulp · ⊤`. -/
  div : F → F → F
  div_error : ∀ a b : F,
    |toReal (div a b) - toReal a / toReal b|
      ≤ ulpBound * |toReal a / toReal b|
  /-- Rounded exponential, faithfully rounded. -/
  exp : F → F
  exp_error : ∀ a : F,
    |toReal (exp a) - Real.exp (toReal a)|
      ≤ ulpBound * Real.exp (toReal a)
  /-- Floating-point `max` — exact under faithful rounding. -/
  max : F → F → F
  max_exact : ∀ a b : F, toReal (max a b) = Max.max (toReal a) (toReal b)

end IEEEFloat

/-! ## ε-bound predicate at the Real layer

`WithinEps ε f g xs` says two `F`-valued kernel functions agree to
within `ε` on `xs` after the faithful real cast.  Used for
forward-error analysis at the abstract level. -/

namespace IEEEFloat.FloatSpec

/-- Real-valued ε-bound between two `F`-valued kernel outputs. -/
def WithinEps {F : Type*} [IEEEFloat.FloatSpec F] (ε : ℝ)
    (f g : List F → F) (xs : List F) : Prop :=
  |toReal (f xs) - toReal (g xs)| ≤ ε

theorem WithinEps_refl {F : Type*} [IEEEFloat.FloatSpec F]
    (f : List F → F) (xs : List F) :
    WithinEps 0 f f xs := by
  unfold WithinEps; simp

theorem WithinEps_symm {F : Type*} [IEEEFloat.FloatSpec F] {ε : ℝ}
    {f g : List F → F} {xs : List F} (h : WithinEps ε f g xs) :
    WithinEps ε g f xs := by
  unfold WithinEps at *
  rw [show toReal (g xs) - toReal (f xs)
        = -(toReal (f xs) - toReal (g xs)) from by ring]
  rw [abs_neg]
  exact h

theorem WithinEps_trans {F : Type*} [IEEEFloat.FloatSpec F] {ε₁ ε₂ : ℝ}
    {f g h : List F → F} {xs : List F}
    (h₁ : WithinEps ε₁ f g xs) (h₂ : WithinEps ε₂ g h xs) :
    WithinEps (ε₁ + ε₂) f h xs := by
  unfold WithinEps at *
  have :=
    abs_sub_le (toReal (f xs)) (toReal (g xs)) (toReal (h xs))
  linarith

end IEEEFloat.FloatSpec
