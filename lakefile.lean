import Lake
open Lake DSL

/-! Lean 4 / Mathlib formalizations of strict IEEE 754 binary floats
    (`IEEEFloat`), low-precision scalar formats (`LowFloat`), and
    block-scaled formats (`MX`, `NV`). -/

package «LeanFloats» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require "leanprover-community" / "mathlib" @ git "v4.28.0"

@[default_target]
lean_lib IEEEFloat where
  roots := #[`IEEEFloat]
  globs := #[.andSubmodules `IEEEFloat]

@[default_target]
lean_lib LowFloat where
  roots := #[`LowFloat]
  globs := #[.andSubmodules `LowFloat]

@[default_target]
lean_lib MX where
  roots := #[`MX]
  globs := #[.andSubmodules `MX]

@[default_target]
lean_lib NV where
  roots := #[`NV]
  globs := #[.andSubmodules `NV]
