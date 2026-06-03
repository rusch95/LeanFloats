import IEEEFloat.FloatSpec
import IEEEFloat.ErrorBounds
import IEEEFloat.Formats

/-! # `IEEEFloat.FloatSpec` instance for `F32`

  *  32 total bits — 1 sign, 8 exponent, 23 trailing mantissa
  *  bias = 127, range ≈ 1×10⁻³⁸ to 3×10³⁸
  *  unit roundoff `u = 2⁻²⁴` (1 ULP relative bound `2⁻²³`)
  *  the standard ML training and inference precision

The `IEEEFloat.FloatSpec F32` instance is theorem-backed: its
normal-result relative-error bounds are derived from the generic
correct-rounding backend and the half-ULP theorem in
`IEEEFloat.ErrorBounds`. -/

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

/-! ## Per-op error bounds -/

/-- Predicate: the F32 value is a normal IEEE 754 float. -/
def isNormal (x : F32) : Prop := IEEEFloat.isNormal x = true

theorem add_error_normal (a b : F32) (h_norm : isNormal (add a b)) :
  |toReal (add a b) - (toReal a + toReal b)|
    ≤ ulpBound * |toReal a + toReal b| := by
  simpa [toReal, add, ulpBound, isNormal, machineEpsilon] using
    IEEEFloat.add_relative_error_normal (eb := 8) (mb := 23)
      (by decide) (by decide) a b h_norm

theorem sub_error_normal (a b : F32) (h_norm : isNormal (sub a b)) :
  |toReal (sub a b) - (toReal a - toReal b)|
    ≤ ulpBound * |toReal a - toReal b| := by
  simpa [toReal, sub, ulpBound, isNormal, machineEpsilon] using
    IEEEFloat.sub_relative_error_normal (eb := 8) (mb := 23)
      (by decide) (by decide) a b h_norm

theorem mul_error_normal (a b : F32) (h_norm : isNormal (mul a b)) :
  |toReal (mul a b) - toReal a * toReal b|
    ≤ ulpBound * |toReal a * toReal b| := by
  simpa [toReal, mul, ulpBound, isNormal, machineEpsilon] using
    IEEEFloat.mul_relative_error_normal (eb := 8) (mb := 23)
      (by decide) (by decide) a b h_norm

theorem div_error_normal (a b : F32) (h_norm : isNormal (div a b)) :
  |toReal (div a b) - toReal a / toReal b|
    ≤ ulpBound * |toReal a / toReal b| := by
  simpa [toReal, div, ulpBound, isNormal, machineEpsilon] using
    IEEEFloat.div_relative_error_normal (eb := 8) (mb := 23)
      (by decide) (by decide) a b h_norm

end IEEEFloat.F32

/-- Theorem-backed `FloatSpec` instance for f32. -/
noncomputable instance : IEEEFloat.FloatSpec IEEEFloat.F32 where
  toReal := IEEEFloat.F32.toReal
  zero := IEEEFloat.F32.zero
  zero_toReal := IEEEFloat.F32.zero_toReal
  one := IEEEFloat.F32.one
  one_toReal := IEEEFloat.F32.one_toReal
  ulpBound := IEEEFloat.F32.ulpBound
  ulpBound_nonneg := IEEEFloat.F32.ulpBound_nonneg
  isNormal := IEEEFloat.F32.isNormal
  add := IEEEFloat.F32.add
  add_error_normal := IEEEFloat.F32.add_error_normal
  sub := IEEEFloat.F32.sub
  sub_error_normal := IEEEFloat.F32.sub_error_normal
  mul := IEEEFloat.F32.mul
  mul_error_normal := IEEEFloat.F32.mul_error_normal
  div := IEEEFloat.F32.div
  div_error_normal := IEEEFloat.F32.div_error_normal
