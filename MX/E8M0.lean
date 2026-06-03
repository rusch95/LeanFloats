import LowFloat.FP8.OCP.E8M0

/-! # Compatibility re-export for MX E8M0

The canonical scalar type now lives at `LowFloat.FP8.OCP.E8M0`.
This module preserves the historical `MX.E8M0` API as reducible
aliases to the canonical definitions.
-/

namespace MX

/-- Historical MX namespace alias for the shared OCP E8M0 scale. -/
abbrev E8M0 : Type := LowFloat.FP8.OCP.E8M0

namespace E8M0

abbrev bias : Int := LowFloat.FP8.OCP.E8M0.bias
abbrev nanRaw : Fin 256 := LowFloat.FP8.OCP.E8M0.nanRaw
abbrev nan : E8M0 := LowFloat.FP8.OCP.E8M0.nan
abbrev one : E8M0 := LowFloat.FP8.OCP.E8M0.one
abbrev isNaN : E8M0 → Bool := LowFloat.FP8.OCP.E8M0.isNaN

noncomputable abbrev toReal : E8M0 → Option ℝ :=
  LowFloat.FP8.OCP.E8M0.toReal

noncomputable abbrev toRealOrZero : E8M0 → ℝ :=
  LowFloat.FP8.OCP.E8M0.toRealOrZero

export LowFloat.FP8.OCP.E8M0
  (isNaN_nan isNaN_one toReal_range)

theorem one_toReal : ((⟨127⟩ : E8M0)).toReal = some 1 :=
  LowFloat.FP8.OCP.E8M0.one_toReal

theorem nan_toReal : nan.toReal = none :=
  LowFloat.FP8.OCP.E8M0.nan_toReal

end E8M0

end MX
