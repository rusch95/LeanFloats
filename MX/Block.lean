import Mathlib.Data.Vector.Defs
import MX.E2M1
import MX.E8M0

/-! # MXBlock — a block of K E2M1 elements with a shared E8M0 scale

The MX block is the unit of storage and computation in the OCP MX
specification.  An `MXBlock K` consists of:

  *  one `E8M0` scale (8 bits),
  *  K `E2M1` elements (4 bits each), where K = 32 in the standard
     MXFP4 layout.

Storage size: `8 + 4K = 8 + 128 = 136 bits` per block (17 bytes for
K=32, though packing usually pads to 18 or 20 bytes).

Decoded value of element `i` in the block: `scale.toReal * elem[i].toReal`.

If the scale is NaN, the entire block is NaN-tagged: every element
decodes to `none`.
-/

namespace MX

/-- A block of K MXFP4 elements sharing one E8M0 scale.

Standard MXFP4 uses `K = 32`; we leave it as a type parameter so
`MXBlock` can model larger or smaller block sizes (e.g., research
configs with K=16 or K=64). -/
structure MXBlock (K : Nat) where
  scale : E8M0
  elements : List.Vector E2M1 K

namespace MXBlock

variable {K : Nat}

instance : Inhabited (MXBlock K) :=
  ⟨{ scale := E8M0.one, elements := List.Vector.replicate K default }⟩

/-- A block is NaN iff its scale is NaN. -/
def isNaN (b : MXBlock K) : Bool := b.scale.isNaN

@[simp] theorem isNaN_iff (b : MXBlock K) :
    b.isNaN = true ↔ b.scale.isNaN = true := Iff.rfl

/-- The standard MXFP4 block size: 32 elements per block. -/
abbrev MXFP4 : Type := MXBlock 32

end MXBlock

end MX
