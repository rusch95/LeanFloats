import Mathlib.Data.Vector.Defs
import MX.E2M1
import NV.E4M3

/-! # NVBlock — NVFP4 micro-blocks

An NVFP4 micro-block contains:

  * one shared FP8 E4M3 scale,
  * `K` E2M1 FP4 elements.

NVIDIA's NVFP4 layout uses `K = 16`, half the MXFP4 block size.
The per-tensor FP32 scale is intentionally not stored in each block;
decoding takes it as a real-valued parameter.
-/

namespace NV

/-- A block of `K` NVFP4 elements sharing one E4M3 scale. -/
structure NVBlock (K : Nat) where
  scale : E4M3
  elements : List.Vector MX.E2M1 K

namespace NVBlock

variable {K : Nat}

instance : Inhabited (NVBlock K) :=
  ⟨{ scale := E4M3.one, elements := List.Vector.replicate K default }⟩

/-- A block is NaN-tagged iff its E4M3 scale is NaN. -/
def isNaN (b : NVBlock K) : Bool := b.scale.isNaN

@[simp] theorem isNaN_iff (b : NVBlock K) :
    b.isNaN = true ↔ b.scale.isNaN = true := Iff.rfl

/-- The standard NVFP4 micro-block size: 16 elements per E4M3 scale. -/
abbrev NVFP4 : Type := NVBlock 16

end NVBlock

end NV
