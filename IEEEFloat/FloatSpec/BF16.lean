import IEEEFloat.FloatSpec
import IEEEFloat.Backend
import IEEEFloat.Formats

/-! # `IEEEFloat.FloatSpec` instance for `BF16` (brain-float 16)

  *  16 total bits — 1 sign, 8 exp, 7 trailing mantissa
  *  bias = 127 (matches f32; trades mantissa for f32 range)
  *  unit roundoff `u = 2⁻⁸` (1 ULP relative bound `2⁻⁷`)
  *  used widely in ML training (Google TPU, NVIDIA Ampere+)

See `IEEEFloat/FloatSpec/F32.lean` for the rationale on the two
forms of error bounds. -/

namespace IEEEFloat.BF16

noncomputable def toReal : BF16 → ℝ := IEEEFloat.toRealOrZero

noncomputable def ulpBound : ℝ := (2 : ℝ) ^ (-7 : Int)

theorem ulpBound_nonneg : 0 ≤ ulpBound := by unfold ulpBound; positivity

abbrev zero : BF16 := IEEEFloat.BFloat16.zero
abbrev one  : BF16 := IEEEFloat.BFloat16.one

theorem zero_toReal : toReal zero = 0 := IEEEFloat.BFloat16.zero_toReal
theorem one_toReal  : toReal one  = 1 := IEEEFloat.BFloat16.one_toReal

noncomputable def add (a b : BF16) : BF16 :=
  IEEEFloat.add (eb := 8) (mb := 7) (by decide) (by decide) a b
noncomputable def sub (a b : BF16) : BF16 :=
  IEEEFloat.sub (eb := 8) (mb := 7) (by decide) (by decide) a b
noncomputable def mul (a b : BF16) : BF16 :=
  IEEEFloat.mul (eb := 8) (mb := 7) (by decide) (by decide) a b
noncomputable def div (a b : BF16) : BF16 :=
  IEEEFloat.div (eb := 8) (mb := 7) (by decide) (by decide) a b

def isNormal (x : BF16) : Prop := IEEEFloat.isNormal x = true

axiom add_error_normal (a b : BF16) (h_norm : isNormal (add a b)) :
  |toReal (add a b) - (toReal a + toReal b)|
    ≤ ulpBound * |toReal a + toReal b|
axiom sub_error_normal (a b : BF16) (h_norm : isNormal (sub a b)) :
  |toReal (sub a b) - (toReal a - toReal b)|
    ≤ ulpBound * |toReal a - toReal b|
axiom mul_error_normal (a b : BF16) (h_norm : isNormal (mul a b)) :
  |toReal (mul a b) - toReal a * toReal b|
    ≤ ulpBound * |toReal a * toReal b|
axiom div_error_normal (a b : BF16) (h_norm : isNormal (div a b)) :
  |toReal (div a b) - toReal a / toReal b|
    ≤ ulpBound * |toReal a / toReal b|

axiom add_error (a b : BF16) :
  |toReal (add a b) - (toReal a + toReal b)|
    ≤ ulpBound * |toReal a + toReal b|
axiom sub_error (a b : BF16) :
  |toReal (sub a b) - (toReal a - toReal b)|
    ≤ ulpBound * |toReal a - toReal b|
axiom mul_error (a b : BF16) :
  |toReal (mul a b) - toReal a * toReal b|
    ≤ ulpBound * |toReal a * toReal b|
axiom div_error (a b : BF16) :
  |toReal (div a b) - toReal a / toReal b|
    ≤ ulpBound * |toReal a / toReal b|

opaque exp : BF16 → BF16
axiom exp_error_normal (a : BF16) (h_norm : isNormal (exp a)) :
  |toReal (exp a) - Real.exp (toReal a)|
    ≤ ulpBound * Real.exp (toReal a)
axiom exp_error (a : BF16) :
  |toReal (exp a) - Real.exp (toReal a)|
    ≤ ulpBound * Real.exp (toReal a)

opaque max : BF16 → BF16 → BF16
axiom max_exact (a b : BF16) :
  toReal (max a b) = Max.max (toReal a) (toReal b)

end IEEEFloat.BF16

noncomputable instance : IEEEFloat.FloatSpec IEEEFloat.BF16 where
  toReal := IEEEFloat.BF16.toReal
  zero := IEEEFloat.BF16.zero
  zero_toReal := IEEEFloat.BF16.zero_toReal
  one := IEEEFloat.BF16.one
  one_toReal := IEEEFloat.BF16.one_toReal
  ulpBound := IEEEFloat.BF16.ulpBound
  ulpBound_nonneg := IEEEFloat.BF16.ulpBound_nonneg
  add := IEEEFloat.BF16.add
  add_error := IEEEFloat.BF16.add_error
  sub := IEEEFloat.BF16.sub
  sub_error := IEEEFloat.BF16.sub_error
  mul := IEEEFloat.BF16.mul
  mul_error := IEEEFloat.BF16.mul_error
  div := IEEEFloat.BF16.div
  div_error := IEEEFloat.BF16.div_error
  exp := IEEEFloat.BF16.exp
  exp_error := IEEEFloat.BF16.exp_error
  max := IEEEFloat.BF16.max
  max_exact := IEEEFloat.BF16.max_exact
