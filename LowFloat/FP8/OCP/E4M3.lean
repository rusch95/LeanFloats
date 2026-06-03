import NV.E4M3

/-! # OCP FP8 E4M3

Vendor-neutral import path for the OCP FP8 `E4M3` scalar format:

  * 1 sign bit, 4 exponent bits, 3 mantissa bits.
  * Bias = 7.
  * No infinities.
  * NaN encodings are `0x7f` and `0xff`.
  * Maximum positive finite value is `448`.

The current implementation is the same structure already used by the
NVFP4 scale layer.  Keeping this alias lets downstream code import an
OCP-format name without depending on the `NV` namespace.
-/

namespace LowFloat
namespace FP8
namespace OCP

/-- OCP FP8 E4M3 scalar. -/
abbrev E4M3 : Type := NV.E4M3

namespace E4M3

abbrev bias : Int := NV.E4M3.bias
abbrev zero : E4M3 := NV.E4M3.zero
abbrev one : E4M3 := NV.E4M3.one
abbrev nan : E4M3 := NV.E4M3.nan
abbrev maxFinite : E4M3 := NV.E4M3.maxFinite

abbrev isNaN : E4M3 → Bool := NV.E4M3.isNaN
abbrev isZero : E4M3 → Bool := NV.E4M3.isZero
abbrev isSubnormal : E4M3 → Bool := NV.E4M3.isSubnormal
abbrev isNormal : E4M3 → Bool := NV.E4M3.isNormal

noncomputable abbrev finiteValue : E4M3 → ℝ := NV.E4M3.finiteValue
noncomputable abbrev toReal : E4M3 → Option ℝ := NV.E4M3.toReal
noncomputable abbrev toRealOrZero : E4M3 → ℝ := NV.E4M3.toRealOrZero

abbrev toBits : E4M3 → BitVec 8 := NV.E4M3.toBits
abbrev fromBits : BitVec 8 → E4M3 := NV.E4M3.fromBits

theorem zero_toReal : zero.toReal = some 0 := NV.E4M3.zero_toReal
theorem one_toReal : one.toReal = some 1 := NV.E4M3.one_toReal
theorem nan_toReal : nan.toReal = none := NV.E4M3.nan_toReal
theorem maxFinite_toReal : maxFinite.toReal = some 448 :=
  NV.E4M3.maxFinite_toReal

end E4M3

end OCP
end FP8
end LowFloat
