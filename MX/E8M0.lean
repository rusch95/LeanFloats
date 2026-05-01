import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # E8M0 — the 8-bit MX block scale

A pure exponent-only format: 8 bits encoding `2^k` for `k ∈ [-127, 127]`,
plus one reserved NaN pattern.

  *  Bias = 127.
  *  Bit pattern `0x00` (raw exponent 0) → `2^(-127)`.
  *  Bit patterns `0x01` … `0xFE` (raw 1 … 254) → `2^(raw - 127)`.
  *  Bit pattern `0xFF` (raw 255) → NaN.

There is no sign bit and no mantissa bit.  The format exists only to
provide a per-block multiplicative scale factor in the MX format.

When a block's scale is NaN, the entire block is interpreted as
NaN-tagged — every element decode produces `none`.
-/

namespace MX

/-- An E8M0 scale: an 8-bit raw value, with `0xFF` reserved for NaN. -/
structure E8M0 where
  raw : Fin 256
  deriving DecidableEq, Fintype, Repr

namespace E8M0

instance : Inhabited E8M0 := ⟨⟨127⟩⟩  -- 2^0 = 1

/-- Bias for E8M0: 127. -/
def bias : Int := 127

/-- The raw value reserved for NaN. -/
def nanRaw : Fin 256 := 255

/-- A specific E8M0 NaN. -/
def nan : E8M0 := ⟨nanRaw⟩

/-- The "scale = 1" value: raw = 127. -/
def one : E8M0 := ⟨127⟩

/-! ## Predicates -/

def isNaN (x : E8M0) : Bool := x.raw = nanRaw

@[simp] theorem isNaN_nan : isNaN nan = true := by
  unfold isNaN nan; rfl

@[simp] theorem isNaN_one : isNaN one = false := by
  unfold isNaN one nanRaw; rfl

/-! ## Real-valued decoding

NaN decodes to `none`; everything else decodes to `2^(raw - 127)`. -/

/-- Decode an E8M0 to its scale factor.  `none` for NaN, `some (2^k)`
    otherwise. -/
noncomputable def toReal (x : E8M0) : Option ℝ :=
  if x.raw = nanRaw then none
  else some ((2 : ℝ) ^ ((x.raw.val : Int) - bias))

/-- The "raw scalar" form: `0` for NaN, `2^k` otherwise.  Use only
    after dispatching the NaN case; prefer `toReal` for safety. -/
noncomputable def toRealOrZero (x : E8M0) : ℝ :=
  if x.raw = nanRaw then 0
  else (2 : ℝ) ^ ((x.raw.val : Int) - bias)

/-- The scale value for `one` is `2^0 = 1`. -/
theorem one_toReal : one.toReal = some 1 := by
  unfold toReal one bias nanRaw
  simp

theorem nan_toReal : nan.toReal = none := by
  unfold toReal nan nanRaw; simp

/-- Range of representable scales: `2^{-127}` (smallest) to `2^{127}`
    (largest), plus NaN. -/
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
      have h_lt : x.raw.val < 256 := x.raw.isLt
      have h_ne_val : x.raw.val ≠ 255 := fun h_eq => h_ne (Fin.ext h_eq)
      have : (x.raw.val : Int) ≤ 254 := by
        have : x.raw.val ≤ 254 := by omega
        exact_mod_cast this
      linarith
  · unfold toReal
    rw [if_neg h_ne]

end E8M0

end MX
