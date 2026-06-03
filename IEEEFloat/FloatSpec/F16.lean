import IEEEFloat.FloatSpec
import IEEEFloat.ErrorBounds
import IEEEFloat.Formats

/-! # `IEEEFloat.FloatSpec` instance for `F16` (binary16, half precision)

  *  16 total bits — 1 sign, 5 exp, 10 trailing mantissa
  *  bias = 15, range ≈ 6×10⁻⁵ to 6×10⁴
  *  unit roundoff `u = 2⁻¹¹` (1 ULP relative bound `2⁻¹⁰`)
  *  used in graphics, ML inference

The normal-result relative-error bounds are derived from the generic
correct-rounding backend and the half-ULP theorem in
`IEEEFloat.ErrorBounds`. -/

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

theorem add_error_normal (a b : F16) (h_norm : isNormal (add a b)) :
  |toReal (add a b) - (toReal a + toReal b)|
    ≤ ulpBound * |toReal a + toReal b| := by
  simpa [toReal, add, ulpBound, isNormal, machineEpsilon] using
    IEEEFloat.add_relative_error_normal (eb := 5) (mb := 10)
      (by decide) (by decide) a b h_norm

theorem sub_error_normal (a b : F16) (h_norm : isNormal (sub a b)) :
  |toReal (sub a b) - (toReal a - toReal b)|
    ≤ ulpBound * |toReal a - toReal b| := by
  simpa [toReal, sub, ulpBound, isNormal, machineEpsilon] using
    IEEEFloat.sub_relative_error_normal (eb := 5) (mb := 10)
      (by decide) (by decide) a b h_norm

theorem mul_error_normal (a b : F16) (h_norm : isNormal (mul a b)) :
  |toReal (mul a b) - toReal a * toReal b|
    ≤ ulpBound * |toReal a * toReal b| := by
  simpa [toReal, mul, ulpBound, isNormal, machineEpsilon] using
    IEEEFloat.mul_relative_error_normal (eb := 5) (mb := 10)
      (by decide) (by decide) a b h_norm

theorem div_error_normal (a b : F16) (h_norm : isNormal (div a b)) :
  |toReal (div a b) - toReal a / toReal b|
    ≤ ulpBound * |toReal a / toReal b| := by
  simpa [toReal, div, ulpBound, isNormal, machineEpsilon] using
    IEEEFloat.div_relative_error_normal (eb := 5) (mb := 10)
      (by decide) (by decide) a b h_norm

end IEEEFloat.F16

noncomputable instance : IEEEFloat.FloatSpec IEEEFloat.F16 where
  toReal := IEEEFloat.F16.toReal
  zero := IEEEFloat.F16.zero
  zero_toReal := IEEEFloat.F16.zero_toReal
  one := IEEEFloat.F16.one
  one_toReal := IEEEFloat.F16.one_toReal
  ulpBound := IEEEFloat.F16.ulpBound
  ulpBound_nonneg := IEEEFloat.F16.ulpBound_nonneg
  isNormal := IEEEFloat.F16.isNormal
  add := IEEEFloat.F16.add
  add_error_normal := IEEEFloat.F16.add_error_normal
  sub := IEEEFloat.F16.sub
  sub_error_normal := IEEEFloat.F16.sub_error_normal
  mul := IEEEFloat.F16.mul
  mul_error_normal := IEEEFloat.F16.mul_error_normal
  div := IEEEFloat.F16.div
  div_error_normal := IEEEFloat.F16.div_error_normal
