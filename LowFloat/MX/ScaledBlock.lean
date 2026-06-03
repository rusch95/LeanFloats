import Mathlib.Data.Vector.Basic
import LowFloat.FP4.E2M1
import LowFloat.FP6.E2M3
import LowFloat.FP6.E3M2
import LowFloat.FP8.OCP.E4M3
import LowFloat.FP8.OCP.E5M2
import LowFloat.FP8.OCP.E8M0

/-! # Generic microscaling block shells

This module captures the storage/decode shape common to OCP-style
microscaling formats without introducing kernel-level operations.

An MX block stores:

  * one `E8M0` scale, and
  * `K` low-precision scalar elements.

This file intentionally stops at decode semantics.  Matrix kernels,
reduction order, and accumulator formats belong in downstream repos
or in higher-level modules.
-/

namespace LowFloat
namespace MX

/-- A block of `K` elements sharing one unsigned exponent-only E8M0 scale. -/
structure ScaledBlock (α : Type) (K : Nat) where
  scale : FP8.OCP.E8M0
  elements : List.Vector α K

namespace ScaledBlock

variable {α : Type} {K : Nat}

instance [Inhabited α] : Inhabited (ScaledBlock α K) :=
  ⟨{ scale := FP8.OCP.E8M0.one, elements := List.Vector.replicate K default }⟩

def isNaN (b : ScaledBlock α K) : Bool := b.scale.isNaN

/-- Decode a block whose element format has no special values. -/
noncomputable def decodeAtFinite (elemToReal : α → ℝ)
    (b : ScaledBlock α K) (i : Fin K) : Option ℝ :=
  match b.scale.toReal with
  | none => none
  | some s => some (s * elemToReal (b.elements.get i))

/-- Decode a block whose element format may itself decode to `none`. -/
noncomputable def decodeAtOption (elemToReal : α → Option ℝ)
    (b : ScaledBlock α K) (i : Fin K) : Option ℝ :=
  match b.scale.toReal, elemToReal (b.elements.get i) with
  | some s, some x => some (s * x)
  | _, _ => none

noncomputable def decodeFinite (elemToReal : α → ℝ)
    (b : ScaledBlock α K) : List.Vector (Option ℝ) K :=
  List.Vector.ofFn fun i => b.decodeAtFinite elemToReal i

noncomputable def decodeOption (elemToReal : α → Option ℝ)
    (b : ScaledBlock α K) : List.Vector (Option ℝ) K :=
  List.Vector.ofFn fun i => b.decodeAtOption elemToReal i

end ScaledBlock

/-! ## Common named block formats -/

/-- OCP MXFP4: 32 E2M1 values sharing one E8M0 scale. -/
abbrev MXFP4 : Type := ScaledBlock FP4.E2M1 32

/-- OCP/NVIDIA/AMD FP6 E2M3 microscaling block shell. -/
abbrev MXFP6E2M3 : Type := ScaledBlock FP6.E2M3 32

/-- OCP/NVIDIA/AMD FP6 E3M2 microscaling block shell. -/
abbrev MXFP6E3M2 : Type := ScaledBlock FP6.E3M2 32

/-- NVIDIA Blackwell-style MXFP8: 32 E4M3 values sharing one E8M0 scale. -/
abbrev MXFP8E4M3 : Type := ScaledBlock FP8.OCP.E4M3 32

/-- An E5M2 block shell for software stacks that use E5M2 with E8M0 scales. -/
abbrev MXFP8E5M2 : Type := ScaledBlock FP8.OCP.E5M2 32

namespace MXFP4

noncomputable def decodeAt (b : MXFP4) (i : Fin 32) : Option ℝ :=
  b.decodeAtFinite FP4.E2M1.toReal i

end MXFP4

namespace MXFP6E2M3

noncomputable def decodeAt (b : MXFP6E2M3) (i : Fin 32) : Option ℝ :=
  b.decodeAtFinite FP6.E2M3.toReal i

end MXFP6E2M3

namespace MXFP6E3M2

noncomputable def decodeAt (b : MXFP6E3M2) (i : Fin 32) : Option ℝ :=
  b.decodeAtFinite FP6.E3M2.toReal i

end MXFP6E3M2

namespace MXFP8E4M3

noncomputable def decodeAt (b : MXFP8E4M3) (i : Fin 32) : Option ℝ :=
  b.decodeAtOption FP8.OCP.E4M3.toReal i

end MXFP8E4M3

namespace MXFP8E5M2

noncomputable def decodeAt (b : MXFP8E5M2) (i : Fin 32) : Option ℝ :=
  b.decodeAtOption FP8.OCP.E5M2.toReal i

end MXFP8E5M2

end MX
end LowFloat
