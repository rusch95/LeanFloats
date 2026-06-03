import LowFloat.FP4.E2M1

/-! # Compatibility re-export for MXFP4 E2M1

The canonical scalar type now lives at `LowFloat.FP4.E2M1`.  This
module preserves the historical `MX.E2M1` API, including concrete
wrapper definitions that old MX proofs unfold directly.
-/

namespace MX

/-- Historical MX namespace alias for the shared FP4 E2M1 scalar. -/
abbrev E2M1 : Type := LowFloat.FP4.E2M1

namespace E2M1

instance : Inhabited E2M1 := ⟨⟨false, 0, 0⟩⟩

/-- Bias for E2M1: `2^(2-1) - 1 = 1`. -/
def bias : Int := 1

/-- Decode an E2M1 to its real-valued interpretation. -/
noncomputable def toReal (x : E2M1) : ℝ :=
  let sign : ℝ := if x.s then -1 else 1
  let mantissa : ℝ := (x.m.val : ℝ) / 2
  if x.e.val = 0 then
    sign * mantissa
  else
    sign * (2 : ℝ) ^ ((x.e.val : Int) - bias) * (1 + mantissa)

theorem toReal_pos_zero :
    toReal ⟨false, 0, 0⟩ = 0 := by
  unfold toReal; simp
theorem toReal_neg_zero :
    toReal ⟨true, 0, 0⟩ = 0 := by
  unfold toReal; simp
theorem toReal_pos_half :
    toReal ⟨false, 0, 1⟩ = 1 / 2 := by
  unfold toReal; norm_num
theorem toReal_neg_half :
    toReal ⟨true, 0, 1⟩ = -(1 / 2) := by
  unfold toReal; norm_num
theorem toReal_pos_one :
    toReal ⟨false, 1, 0⟩ = 1 := by
  unfold toReal bias; norm_num
theorem toReal_pos_three_halves :
    toReal ⟨false, 1, 1⟩ = 3 / 2 := by
  unfold toReal bias; norm_num
theorem toReal_pos_two :
    toReal ⟨false, 2, 0⟩ = 2 := by
  unfold toReal bias; norm_num
theorem toReal_pos_three :
    toReal ⟨false, 2, 1⟩ = 3 := by
  unfold toReal bias; norm_num
theorem toReal_pos_four :
    toReal ⟨false, 3, 0⟩ = 4 := by
  unfold toReal bias; norm_num
theorem toReal_pos_six :
    toReal ⟨false, 3, 1⟩ = 6 := by
  unfold toReal bias; norm_num
theorem toReal_neg_six :
    toReal ⟨true, 3, 1⟩ = -6 := by
  unfold toReal bias; norm_num

/-- Maximum representable magnitude: `+6`. -/
noncomputable def maxValue : ℝ := 6

/-- Smallest positive value: `+0.5` (the only subnormal magnitude). -/
noncomputable def minPositive : ℝ := 1 / 2

/-- `e = 0, m = 0`: `±0`. -/
def isZero (x : E2M1) : Bool := x.e.val = 0 ∧ x.m.val = 0

/-- `e = 0, m ≠ 0`: subnormal (only `±0.5`). -/
def isSubnormal (x : E2M1) : Bool := x.e.val = 0 ∧ x.m.val ≠ 0

/-- `e ≠ 0`: normal. -/
def isNormal (x : E2M1) : Bool := x.e.val ≠ 0

/-- `s = false`: positive sign. -/
def isPositive (x : E2M1) : Bool := !x.s

/-! ## Negation -/

def neg (x : E2M1) : E2M1 := { x with s := !x.s }

instance : Neg E2M1 := ⟨neg⟩

@[simp] theorem neg_eq (x : E2M1) : -x = ⟨!x.s, x.e, x.m⟩ := rfl

theorem neg_neg (x : E2M1) : - -x = x := by
  cases x; simp

/-- Sign flip negates the real value. -/
theorem toReal_neg (x : E2M1) : (-x).toReal = -(x.toReal) := by
  rcases x with ⟨s, e, m⟩
  show toReal ⟨!s, e, m⟩ = -(toReal ⟨s, e, m⟩)
  unfold toReal
  rcases s with _ | _
  · simp; split_ifs <;> ring
  · simp; split_ifs <;> ring

/-! ## Bit-pattern packing -/

/-- Pack to 4 bits.  Bit layout: `s e₁ e₀ m₀`. -/
def toBits (x : E2M1) : BitVec 4 :=
  BitVec.ofBool x.s ++ BitVec.ofNat 2 x.e.val ++ BitVec.ofNat 1 x.m.val

/-- Decode from 4 bits. -/
def fromBits (b : BitVec 4) : E2M1 where
  s := b.getLsbD 3
  e := ⟨((b.toNat >>> 1) &&& 0b11), by
    have : (b.toNat >>> 1) &&& 3 ≤ 3 := Nat.and_le_right
    omega⟩
  m := ⟨b.toNat &&& 1, by
    have : b.toNat &&& 1 ≤ 1 := Nat.and_le_right
    omega⟩

end E2M1

end MX
