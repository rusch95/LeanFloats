import IEEEFloat.FloatSpec
import IEEEFloat.ErrorBounds
import IEEEFloat.Formats

/-! # `IEEEFloat.FloatSpec` instance for `BF16` (brain-float 16)

  *  16 total bits — 1 sign, 8 exp, 7 trailing mantissa
  *  bias = 127 (matches f32; trades mantissa for f32 range)
  *  unit roundoff `u = 2⁻⁸` (1 ULP relative bound `2⁻⁷`)
  *  used widely in ML training (Google TPU, NVIDIA Ampere+)

The normal-result relative-error bounds are derived from the generic
correct-rounding backend and the half-ULP theorem in
`IEEEFloat.ErrorBounds`. -/

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

theorem add_error_normal (a b : BF16) (h_norm : isNormal (add a b)) :
  |toReal (add a b) - (toReal a + toReal b)|
    ≤ ulpBound * |toReal a + toReal b| := by
  simpa [toReal, add, ulpBound, isNormal, machineEpsilon] using
    IEEEFloat.add_relative_error_normal (eb := 8) (mb := 7)
      (by decide) (by decide) a b h_norm

theorem sub_error_normal (a b : BF16) (h_norm : isNormal (sub a b)) :
  |toReal (sub a b) - (toReal a - toReal b)|
    ≤ ulpBound * |toReal a - toReal b| := by
  simpa [toReal, sub, ulpBound, isNormal, machineEpsilon] using
    IEEEFloat.sub_relative_error_normal (eb := 8) (mb := 7)
      (by decide) (by decide) a b h_norm

theorem mul_error_normal (a b : BF16) (h_norm : isNormal (mul a b)) :
  |toReal (mul a b) - toReal a * toReal b|
    ≤ ulpBound * |toReal a * toReal b| := by
  simpa [toReal, mul, ulpBound, isNormal, machineEpsilon] using
    IEEEFloat.mul_relative_error_normal (eb := 8) (mb := 7)
      (by decide) (by decide) a b h_norm

theorem div_error_normal (a b : BF16) (h_norm : isNormal (div a b)) :
  |toReal (div a b) - toReal a / toReal b|
    ≤ ulpBound * |toReal a / toReal b| := by
  simpa [toReal, div, ulpBound, isNormal, machineEpsilon] using
    IEEEFloat.div_relative_error_normal (eb := 8) (mb := 7)
      (by decide) (by decide) a b h_norm

end IEEEFloat.BF16

noncomputable instance : IEEEFloat.FloatSpec IEEEFloat.BF16 where
  toReal := IEEEFloat.BF16.toReal
  zero := IEEEFloat.BF16.zero
  zero_toReal := IEEEFloat.BF16.zero_toReal
  one := IEEEFloat.BF16.one
  one_toReal := IEEEFloat.BF16.one_toReal
  ulpBound := IEEEFloat.BF16.ulpBound
  ulpBound_nonneg := IEEEFloat.BF16.ulpBound_nonneg
  isNormal := IEEEFloat.BF16.isNormal
  add := IEEEFloat.BF16.add
  add_error_normal := IEEEFloat.BF16.add_error_normal
  sub := IEEEFloat.BF16.sub
  sub_error_normal := IEEEFloat.BF16.sub_error_normal
  mul := IEEEFloat.BF16.mul
  mul_error_normal := IEEEFloat.BF16.mul_error_normal
  div := IEEEFloat.BF16.div
  div_error_normal := IEEEFloat.BF16.div_error_normal
