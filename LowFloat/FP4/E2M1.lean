import MX.E2M1

/-! # Shared E2M1 FP4 scalar format

This module gives the OCP/NVIDIA/AMD scalar FP4 `E2M1` format a
vendor-neutral import path.  The implementation is the already-proved
`MX.E2M1` element format:

  * 1 sign bit, 2 exponent bits, 1 mantissa bit.
  * Bias = 1.
  * No infinities and no NaNs; every 4-bit pattern is finite.
  * Values are `{0, ±0.5, ±1, ±1.5, ±2, ±3, ±4, ±6}`.

`MX` keeps its historical namespace for compatibility.  New format
coverage code should prefer `LowFloat.FP4.E2M1`.
-/

namespace LowFloat
namespace FP4

/-- Vendor-neutral alias for the OCP/NVIDIA/AMD E2M1 FP4 scalar. -/
abbrev E2M1 : Type := MX.E2M1

namespace E2M1

abbrev bias : Int := MX.E2M1.bias

noncomputable abbrev toReal : E2M1 → ℝ := MX.E2M1.toReal

abbrev toBits : E2M1 → BitVec 4 := MX.E2M1.toBits
abbrev fromBits : BitVec 4 → E2M1 := MX.E2M1.fromBits

noncomputable abbrev maxValue : ℝ := MX.E2M1.maxValue
noncomputable abbrev minPositive : ℝ := MX.E2M1.minPositive

abbrev isZero : E2M1 → Bool := MX.E2M1.isZero
abbrev isSubnormal : E2M1 → Bool := MX.E2M1.isSubnormal
abbrev isNormal : E2M1 → Bool := MX.E2M1.isNormal

theorem toReal_pos_zero : toReal ⟨false, 0, 0⟩ = 0 :=
  MX.E2M1.toReal_pos_zero

theorem toReal_pos_half : toReal ⟨false, 0, 1⟩ = 1 / 2 :=
  MX.E2M1.toReal_pos_half

theorem toReal_pos_six : toReal ⟨false, 3, 1⟩ = 6 :=
  MX.E2M1.toReal_pos_six

theorem toReal_neg_six : toReal ⟨true, 3, 1⟩ = -6 :=
  MX.E2M1.toReal_neg_six

end E2M1

end FP4
end LowFloat
