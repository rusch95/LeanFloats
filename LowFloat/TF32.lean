import IEEEFloat.Formats

/-! # TensorFloat-32

TF32 keeps FP32's 8-bit exponent field but uses a 10-bit trailing
mantissa.  Tensor cores commonly treat it as a compute format stored
in 32-bit lanes, with FP32 inputs rounded to the shorter mantissa.

At the scalar-format level this is exactly `IEEEFloat 8 10`.
Rounding from FP32 into TF32 is a separate operation and should be
specified on top of this alias.
-/

namespace LowFloat

/-- TensorFloat-32 scalar format: FP32 exponent range, 10 mantissa bits. -/
abbrev TF32 : Type := _root_.IEEEFloat 8 10

namespace TF32

theorem bias_eq : (IEEEFloat.bias 8 : Int) = 127 := by decide
theorem maxExp_eq : (IEEEFloat.maxExp 8 : Int) = 127 := by decide
theorem minNormalExp_eq : (IEEEFloat.minNormalExp 8 : Int) = -126 := by decide
theorem minSubnormalExp_eq :
    (IEEEFloat.minSubnormalExp 8 10 : Int) = -136 := by decide

def zero : TF32 := _root_.IEEEFloat.finite false ⟨0, by decide⟩ ⟨0, by decide⟩
def one : TF32 := _root_.IEEEFloat.finite false ⟨127, by decide⟩ ⟨0, by decide⟩
def maxFiniteEnc : TF32 :=
  _root_.IEEEFloat.finite false ⟨2 ^ 8 - 1 - 1, by decide⟩ ⟨2 ^ 10 - 1, by decide⟩

theorem zero_toReal : zero.toRealOrZero = 0 := by
  unfold zero IEEEFloat.toRealOrZero IEEEFloat.finiteValue
  simp

theorem one_toReal : one.toRealOrZero = 1 := by
  unfold one IEEEFloat.toRealOrZero IEEEFloat.finiteValue
  simp [IEEEFloat.bias]

theorem maxFinite_eq :
    IEEEFloat.maxFinite 8 10 = (2 - (2:ℝ) ^ (-(10:Int))) * (2:ℝ) ^ (127:Int) := by
  unfold IEEEFloat.maxFinite
  norm_num [IEEEFloat.maxExp, IEEEFloat.bias]

end TF32

end LowFloat
