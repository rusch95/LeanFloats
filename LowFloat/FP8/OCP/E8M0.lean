import Mathlib.Data.Real.Basic
import Mathlib.Data.BitVec
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # OCP E8M0 scale

An unsigned exponent-only 8-bit scale format:

  * 8 exponent bits, 0 mantissa bits, no sign bit.
  * Bias = 127.
  * Bit pattern `0x00` decodes to `2^(-127)`.
  * Bit patterns `0x01` through `0xFE` decode to `2^(raw - 127)`.
  * Bit pattern `0xFF` is NaN.

This format is used by OCP MX formats and NVIDIA MXFP8-style block
scaling.
-/

namespace LowFloat
namespace FP8
namespace OCP

/-- An E8M0 scale: an 8-bit raw value, with `0xFF` reserved for NaN. -/
structure E8M0 where
  raw : Fin 256
  deriving DecidableEq, Fintype, Repr

namespace E8M0

instance : Inhabited E8M0 := ⟨⟨127⟩⟩

/-- Bias for E8M0: 127. -/
def bias : Int := 127

/-- The raw value reserved for NaN. -/
def nanRaw : Fin 256 := 255

/-- A specific E8M0 NaN. -/
def nan : E8M0 := ⟨nanRaw⟩

/-- The scale value `1`: raw = 127. -/
def one : E8M0 := ⟨127⟩

def isNaN (x : E8M0) : Bool := x.raw = nanRaw

@[simp] theorem isNaN_nan : isNaN nan = true := by
  unfold isNaN nan
  rfl

@[simp] theorem isNaN_one : isNaN one = false := by
  unfold isNaN one nanRaw
  rfl

/-- Decode an E8M0 to its scale factor.  `none` for NaN. -/
noncomputable def toReal (x : E8M0) : Option ℝ :=
  if x.raw = nanRaw then none
  else some ((2 : ℝ) ^ ((x.raw.val : Int) - bias))

/-- Decode with `0` as a sentinel for NaN.  Prefer `toReal` unless the
    NaN case has already been discharged. -/
noncomputable def toRealOrZero (x : E8M0) : ℝ :=
  if x.raw = nanRaw then 0
  else (2 : ℝ) ^ ((x.raw.val : Int) - bias)

theorem one_toReal : one.toReal = some 1 := by
  unfold toReal one bias nanRaw
  simp

theorem nan_toReal : nan.toReal = none := by
  unfold toReal nan nanRaw
  simp

/-- Range of representable non-NaN scales: `2^{-127}` to `2^{127}`. -/
theorem toReal_range (x : E8M0) (hx : x.isNaN = false) :
    ∃ k : Int, (-127 ≤ k ∧ k ≤ 127) ∧ x.toReal = some ((2 : ℝ) ^ k) := by
  have h_ne : x.raw ≠ nanRaw := by
    intro h
    simp [isNaN, h] at hx
  refine ⟨(x.raw.val : Int) - bias, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · unfold bias
      have : (0 : Int) ≤ x.raw.val := Int.natCast_nonneg _
      linarith
    · unfold bias
      have h_ne_val : x.raw.val ≠ 255 := fun h_eq => h_ne (Fin.ext h_eq)
      have : (x.raw.val : Int) ≤ 254 := by
        have : x.raw.val ≤ 254 := by omega
        exact_mod_cast this
      linarith
  · unfold toReal
    rw [if_neg h_ne]

/-- Pack to 8 bits. -/
def toBits (x : E8M0) : BitVec 8 := BitVec.ofFin x.raw

/-- Decode from 8 bits. -/
def fromBits (b : BitVec 8) : E8M0 := ⟨b.toFin⟩

end E8M0

end OCP
end FP8
end LowFloat
