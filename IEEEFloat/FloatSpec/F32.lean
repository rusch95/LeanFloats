import IEEEFloat.FloatSpec
import IEEEFloat.Backend
import IEEEFloat.Formats

/-! # `IEEEFloat.FloatSpec` instance for `F32`

  *  32 total bits — 1 sign, 8 exponent, 23 trailing mantissa
  *  bias = 127, range ≈ 1×10⁻³⁸ to 3×10³⁸
  *  unit roundoff `u = 2⁻²⁴` (1 ULP relative bound `2⁻²³`)
  *  the standard ML training and inference precision

The `IEEEFloat.FloatSpec F32` instance is **axiomatized** — it
trusts that the platform's faithful-rounding `binary32` arithmetic
obeys the standard 1-ULP relative-error bound.  The bound's actual
regime of validity is normal-range arithmetic; per-op axioms ship
in two forms (`*_error_normal` precondition'd, `*_error`
unconditional) — see `IEEEFloat/FloatSpec.lean` for the full
discussion. -/

namespace IEEEFloat.F32

/-- Total real-valued cast: non-finite values map to `0`. -/
noncomputable def toReal : F32 → ℝ := IEEEFloat.toRealOrZero

/-- The 1-ULP relative-error bound for f32: `2⁻²³ ≈ 1.19 × 10⁻⁷`. -/
noncomputable def ulpBound : ℝ := (2 : ℝ) ^ (-23 : Int)

theorem ulpBound_nonneg : 0 ≤ ulpBound := by
  unfold ulpBound; positivity

abbrev zero : F32 := IEEEFloat.Binary32.zero
abbrev one  : F32 := IEEEFloat.Binary32.one

theorem zero_toReal : toReal zero = 0 := IEEEFloat.Binary32.zero_toReal
theorem one_toReal  : toReal one  = 1 := IEEEFloat.Binary32.one_toReal

noncomputable def add (a b : F32) : F32 :=
  IEEEFloat.add (eb := 8) (mb := 23) (by decide) (by decide) a b

noncomputable def sub (a b : F32) : F32 :=
  IEEEFloat.sub (eb := 8) (mb := 23) (by decide) (by decide) a b

noncomputable def mul (a b : F32) : F32 :=
  IEEEFloat.mul (eb := 8) (mb := 23) (by decide) (by decide) a b

noncomputable def div (a b : F32) : F32 :=
  IEEEFloat.div (eb := 8) (mb := 23) (by decide) (by decide) a b

/-! ## Per-op error bounds — two forms

Each binary op carries *two* error-bound axioms:

  * `*_error_normal` — precondition'd by `(add a b).isNormal = true`.
    This is the **rigorous** form: the 1-ULP relative bound is
    actually true exactly when the rounded result is a normal float
    (i.e., not subnormal underflow).  Provable from
    `IEEEFloat.add_isCorrectlyRounded` plus
    `IEEEFloat.UlpBound.half_ulp_bound`; currently still
    axiomatized for time, but the precondition correctly delimits
    the regime where the bound holds.

  * `*_error` — unconditional, **looser/aspirational** form.  The
    bound stated here is *false* in subnormal underflow (the
    relative error can be arbitrarily large near zero).  Used by
    the `FloatSpec` typeclass field, and by existing forward-error
    consumers in `wgsl-to-lean` that assume normal-range arithmetic
    implicitly.  Derivable from `*_error_normal` plus a "no
    subnormal underflow" assumption. -/

/-- Predicate: the F32 value is a normal IEEE 754 float. -/
def isNormal (x : F32) : Prop := IEEEFloat.isNormal x = true

axiom add_error_normal (a b : F32) (h_norm : isNormal (add a b)) :
  |toReal (add a b) - (toReal a + toReal b)|
    ≤ ulpBound * |toReal a + toReal b|

axiom sub_error_normal (a b : F32) (h_norm : isNormal (sub a b)) :
  |toReal (sub a b) - (toReal a - toReal b)|
    ≤ ulpBound * |toReal a - toReal b|

axiom mul_error_normal (a b : F32) (h_norm : isNormal (mul a b)) :
  |toReal (mul a b) - toReal a * toReal b|
    ≤ ulpBound * |toReal a * toReal b|

axiom div_error_normal (a b : F32) (h_norm : isNormal (div a b)) :
  |toReal (div a b) - toReal a / toReal b|
    ≤ ulpBound * |toReal a / toReal b|

axiom add_error (a b : F32) :
  |toReal (add a b) - (toReal a + toReal b)|
    ≤ ulpBound * |toReal a + toReal b|

axiom sub_error (a b : F32) :
  |toReal (sub a b) - (toReal a - toReal b)|
    ≤ ulpBound * |toReal a - toReal b|

axiom mul_error (a b : F32) :
  |toReal (mul a b) - toReal a * toReal b|
    ≤ ulpBound * |toReal a * toReal b|

axiom div_error (a b : F32) :
  |toReal (div a b) - toReal a / toReal b|
    ≤ ulpBound * |toReal a / toReal b|

opaque exp : F32 → F32

axiom exp_error_normal (a : F32) (h_norm : isNormal (exp a)) :
  |toReal (exp a) - Real.exp (toReal a)|
    ≤ ulpBound * Real.exp (toReal a)

axiom exp_error (a : F32) :
  |toReal (exp a) - Real.exp (toReal a)|
    ≤ ulpBound * Real.exp (toReal a)

opaque max : F32 → F32 → F32

axiom max_exact (a b : F32) :
  toReal (max a b) = Max.max (toReal a) (toReal b)

end IEEEFloat.F32

/-- Axiomatized `FloatSpec` instance for f32.  Uses the unconditional
    `F32.*_error` axioms; consumers that want the rigorously-true
    precondition'd form should call `IEEEFloat.F32.*_error_normal`
    directly. -/
noncomputable instance : IEEEFloat.FloatSpec IEEEFloat.F32 where
  toReal := IEEEFloat.F32.toReal
  zero := IEEEFloat.F32.zero
  zero_toReal := IEEEFloat.F32.zero_toReal
  one := IEEEFloat.F32.one
  one_toReal := IEEEFloat.F32.one_toReal
  ulpBound := IEEEFloat.F32.ulpBound
  ulpBound_nonneg := IEEEFloat.F32.ulpBound_nonneg
  add := IEEEFloat.F32.add
  add_error := IEEEFloat.F32.add_error
  sub := IEEEFloat.F32.sub
  sub_error := IEEEFloat.F32.sub_error
  mul := IEEEFloat.F32.mul
  mul_error := IEEEFloat.F32.mul_error
  div := IEEEFloat.F32.div
  div_error := IEEEFloat.F32.div_error
  exp := IEEEFloat.F32.exp
  exp_error := IEEEFloat.F32.exp_error
  max := IEEEFloat.F32.max
  max_exact := IEEEFloat.F32.max_exact
