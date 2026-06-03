import LowFloat.FP8.OCP.E4M3

/-! # Compatibility re-export for NV E4M3

The canonical OCP FP8 E4M3 scalar type now lives at
`LowFloat.FP8.OCP.E4M3`.  This module preserves the historical
`NV.E4M3` API used by the NVFP4 block layer as reducible aliases to
the canonical definitions.
-/

namespace NV

/-- Historical NV namespace alias for the shared OCP FP8 E4M3 scalar. -/
abbrev E4M3 : Type := LowFloat.FP8.OCP.E4M3

namespace E4M3

abbrev bias : Int := LowFloat.FP8.OCP.E4M3.bias
abbrev nanMantissa : Fin 8 := LowFloat.FP8.OCP.E4M3.nanMantissa

abbrev zero : E4M3 := LowFloat.FP8.OCP.E4M3.zero
abbrev one : E4M3 := LowFloat.FP8.OCP.E4M3.one
abbrev nan : E4M3 := LowFloat.FP8.OCP.E4M3.nan
abbrev maxFinite : E4M3 := LowFloat.FP8.OCP.E4M3.maxFinite

abbrev isNaN : E4M3 → Bool := LowFloat.FP8.OCP.E4M3.isNaN
abbrev isZero : E4M3 → Bool := LowFloat.FP8.OCP.E4M3.isZero
abbrev isSubnormal : E4M3 → Bool := LowFloat.FP8.OCP.E4M3.isSubnormal
abbrev isNormal : E4M3 → Bool := LowFloat.FP8.OCP.E4M3.isNormal

noncomputable abbrev finiteValue : E4M3 → ℝ :=
  LowFloat.FP8.OCP.E4M3.finiteValue

noncomputable abbrev toReal : E4M3 → Option ℝ :=
  LowFloat.FP8.OCP.E4M3.toReal

noncomputable abbrev toRealOrZero : E4M3 → ℝ :=
  LowFloat.FP8.OCP.E4M3.toRealOrZero

abbrev toBits : E4M3 → BitVec 8 := LowFloat.FP8.OCP.E4M3.toBits
abbrev fromBits : BitVec 8 → E4M3 := LowFloat.FP8.OCP.E4M3.fromBits

export LowFloat.FP8.OCP.E4M3
  (isNaN_nan isNaN_one isNaN_zero)

theorem zero_toReal : ((⟨false, 0, 0⟩ : E4M3)).toReal = some 0 :=
  LowFloat.FP8.OCP.E4M3.zero_toReal

theorem one_toReal : ((⟨false, 7, 0⟩ : E4M3)).toReal = some 1 :=
  LowFloat.FP8.OCP.E4M3.one_toReal

theorem nan_toReal : nan.toReal = none :=
  LowFloat.FP8.OCP.E4M3.nan_toReal

theorem maxFinite_toReal : maxFinite.toReal = some 448 :=
  LowFloat.FP8.OCP.E4M3.maxFinite_toReal

end E4M3

end NV
