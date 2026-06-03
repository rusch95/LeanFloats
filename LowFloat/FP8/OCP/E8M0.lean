import MX.E8M0

/-! # OCP/NVIDIA E8M0 scale

Vendor-neutral alias for the unsigned exponent-only `E8M0` scale
format used by OCP MX formats and NVIDIA MXFP8.

  * 8 exponent bits, 0 mantissa bits, no sign bit.
  * Bias = 127.
  * `0xff` is NaN.
  * Other patterns decode to `2^(raw - 127)`.
-/

namespace LowFloat
namespace FP8
namespace OCP

/-- Unsigned exponent-only 8-bit scale format. -/
abbrev E8M0 : Type := MX.E8M0

namespace E8M0

abbrev bias : Int := MX.E8M0.bias
abbrev nanRaw : Fin 256 := MX.E8M0.nanRaw
abbrev nan : E8M0 := MX.E8M0.nan
abbrev one : E8M0 := MX.E8M0.one
abbrev isNaN : E8M0 → Bool := MX.E8M0.isNaN

noncomputable abbrev toReal : E8M0 → Option ℝ := MX.E8M0.toReal
noncomputable abbrev toRealOrZero : E8M0 → ℝ := MX.E8M0.toRealOrZero

theorem one_toReal : one.toReal = some 1 := MX.E8M0.one_toReal
theorem nan_toReal : nan.toReal = none := MX.E8M0.nan_toReal

end E8M0

end OCP
end FP8
end LowFloat
