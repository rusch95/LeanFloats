import Lake
open Lake DSL

/-! Lean 4 / Mathlib formalizations of strict IEEE 754 binary floats
    (`IEEEFloat`) and the OCP Microscaling FP4 spec (`MX`). -/

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
lean_lib MX where
  roots := #[`MX]
  globs := #[.andSubmodules `MX]
