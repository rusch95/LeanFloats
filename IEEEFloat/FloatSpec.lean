import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # `FloatSpec`: abstract contract for IEEE 754-style rounded arithmetic

A `FloatSpec F` describes a floating-point type `F` together with its
faithful real-valued cast and normal-result per-op relative-error
bounds (1-ULP under round-to-nearest).  Used to state forward-error theorems
generically over the float format — instantiate at `Binary16` /
`BFloat16` / `Binary32` / `Binary64` (`IEEEFloat.FloatSpec.*`), at
Lean's host `Float`, or at any other faithful-rounding floating-
point representation.

The class lives under `namespace IEEEFloat` because Lean core already
declares a `FloatSpec` structure.

## Why the bounds are normal-result only

Round-to-nearest gives a *half*-ULP absolute bound.  For normal
rounded results this implies the standard weaker relative form
`|fl(exact) - exact| ≤ 2⁻ᵐᵇ · |exact|`.

The corresponding unconditional relative bound is false at
subnormal underflow: take `x = 2^(minSubnormalExp − 1)`; the
absolute error `|RN(x) − x|` is on the order of
`2^(minSubnormalExp − 1)`, while `2⁻ᵐᵇ · |x|` is smaller by a
factor of `2^mb`.  The class therefore exposes only the rigorous
normal-result contract. -/

/-! ## Class definition -/

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
      with normal-result preconditions. -/
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
  /-- Predicate: the value is a normal finite float. -/
  isNormal : F → Prop
  /-- Rounded addition. -/
  add : F → F → F
  add_error_normal : ∀ a b : F, isNormal (add a b) →
    |toReal (add a b) - (toReal a + toReal b)|
      ≤ ulpBound * |toReal a + toReal b|
  /-- Rounded subtraction. -/
  sub : F → F → F
  sub_error_normal : ∀ a b : F, isNormal (sub a b) →
    |toReal (sub a b) - (toReal a - toReal b)|
      ≤ ulpBound * |toReal a - toReal b|
  /-- Rounded multiplication. -/
  mul : F → F → F
  mul_error_normal : ∀ a b : F, isNormal (mul a b) →
    |toReal (mul a b) - toReal a * toReal b|
      ≤ ulpBound * |toReal a * toReal b|
  /-- Rounded division.  Implementation-defined at `b = 0`; the
      normal-result precondition excludes the exceptional NaN/∞
      cases for IEEE formats. -/
  div : F → F → F
  div_error_normal : ∀ a b : F, isNormal (div a b) →
    |toReal (div a b) - toReal a / toReal b|
      ≤ ulpBound * |toReal a / toReal b|

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
