import IEEEFloat.FloatSpec
import IEEEFloat.Backend
import IEEEFloat.Formats

/-! # `IEEEFloat.FloatSpec` instance for `F16` (binary16, half precision)

  *  16 total bits — 1 sign, 5 exp, 10 trailing mantissa
  *  bias = 15, range ≈ 6×10⁻⁵ to 6×10⁴
  *  unit roundoff `u = 2⁻¹¹` (1 ULP relative bound `2⁻¹⁰`)
  *  used in graphics, ML inference

See `IEEEFloat/FloatSpec/F32.lean` for the rationale on the two
forms of error bounds (`*_error_normal` precondition'd vs.
`*_error` unconditional). -/

namespace IEEEFloat.F16

noncomputable def toReal : F16 → ℝ := IEEEFloat.toRealOrZero

noncomputable def ulpBound : ℝ := (2 : ℝ) ^ (-10 : Int)

theorem ulpBound_nonneg : 0 ≤ ulpBound := by unfold ulpBound; positivity

abbrev zero : F16 := IEEEFloat.Binary16.zero
abbrev one  : F16 := IEEEFloat.Binary16.one

theorem zero_toReal : toReal zero = 0 := IEEEFloat.Binary16.zero_toReal
theorem one_toReal  : toReal one  = 1 := IEEEFloat.Binary16.one_toReal

noncomputable def add (a b : F16) : F16 :=
  IEEEFloat.add (eb := 5) (mb := 10) (by decide) (by decide) a b
noncomputable def sub (a b : F16) : F16 :=
  IEEEFloat.sub (eb := 5) (mb := 10) (by decide) (by decide) a b
noncomputable def mul (a b : F16) : F16 :=
  IEEEFloat.mul (eb := 5) (mb := 10) (by decide) (by decide) a b
noncomputable def div (a b : F16) : F16 :=
  IEEEFloat.div (eb := 5) (mb := 10) (by decide) (by decide) a b

def isNormal (x : F16) : Prop := IEEEFloat.isNormal x = true

axiom add_error_normal (a b : F16) (h_norm : isNormal (add a b)) :
  |toReal (add a b) - (toReal a + toReal b)|
    ≤ ulpBound * |toReal a + toReal b|
axiom sub_error_normal (a b : F16) (h_norm : isNormal (sub a b)) :
  |toReal (sub a b) - (toReal a - toReal b)|
    ≤ ulpBound * |toReal a - toReal b|
axiom mul_error_normal (a b : F16) (h_norm : isNormal (mul a b)) :
  |toReal (mul a b) - toReal a * toReal b|
    ≤ ulpBound * |toReal a * toReal b|
axiom div_error_normal (a b : F16) (h_norm : isNormal (div a b)) :
  |toReal (div a b) - toReal a / toReal b|
    ≤ ulpBound * |toReal a / toReal b|

axiom add_error (a b : F16) :
  |toReal (add a b) - (toReal a + toReal b)|
    ≤ ulpBound * |toReal a + toReal b|
axiom sub_error (a b : F16) :
  |toReal (sub a b) - (toReal a - toReal b)|
    ≤ ulpBound * |toReal a - toReal b|
axiom mul_error (a b : F16) :
  |toReal (mul a b) - toReal a * toReal b|
    ≤ ulpBound * |toReal a * toReal b|
axiom div_error (a b : F16) :
  |toReal (div a b) - toReal a / toReal b|
    ≤ ulpBound * |toReal a / toReal b|

opaque exp : F16 → F16
axiom exp_error_normal (a : F16) (h_norm : isNormal (exp a)) :
  |toReal (exp a) - Real.exp (toReal a)|
    ≤ ulpBound * Real.exp (toReal a)
axiom exp_error (a : F16) :
  |toReal (exp a) - Real.exp (toReal a)|
    ≤ ulpBound * Real.exp (toReal a)

opaque max : F16 → F16 → F16
axiom max_exact (a b : F16) :
  toReal (max a b) = Max.max (toReal a) (toReal b)

end IEEEFloat.F16

noncomputable instance : IEEEFloat.FloatSpec IEEEFloat.F16 where
  toReal := IEEEFloat.F16.toReal
  zero := IEEEFloat.F16.zero
  zero_toReal := IEEEFloat.F16.zero_toReal
  one := IEEEFloat.F16.one
  one_toReal := IEEEFloat.F16.one_toReal
  ulpBound := IEEEFloat.F16.ulpBound
  ulpBound_nonneg := IEEEFloat.F16.ulpBound_nonneg
  add := IEEEFloat.F16.add
  add_error := IEEEFloat.F16.add_error
  sub := IEEEFloat.F16.sub
  sub_error := IEEEFloat.F16.sub_error
  mul := IEEEFloat.F16.mul
  mul_error := IEEEFloat.F16.mul_error
  div := IEEEFloat.F16.div
  div_error := IEEEFloat.F16.div_error
  exp := IEEEFloat.F16.exp
  exp_error := IEEEFloat.F16.exp_error
  max := IEEEFloat.F16.max
  max_exact := IEEEFloat.F16.max_exact
