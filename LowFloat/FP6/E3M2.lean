import Mathlib.Data.Real.Basic
import Mathlib.Data.BitVec
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! # E3M2 — 6-bit low-precision scalar

OCP/NVIDIA/AMD `E3M2` is a 6-bit floating-point format:

  * 1 sign bit, 3 exponent bits, 2 mantissa bits.
  * Bias = 3.
  * No infinities and no NaNs; every bit pattern is finite.

It is one of the FP6 formats exposed by AMD CDNA4/HIP and NVIDIA PTX.
Compared with `E2M3`, it trades one mantissa bit for wider range.
-/

namespace LowFloat
namespace FP6

/-- An E3M2 value: sign + 3-bit exponent + 2-bit mantissa. -/
structure E3M2 where
  s : Bool
  e : Fin 8
  m : Fin 4
  deriving DecidableEq, Fintype, Repr

namespace E3M2

instance : Inhabited E3M2 := ⟨⟨false, 0, 0⟩⟩

/-- Bias for E3M2. -/
def bias : Int := 3

/-- Decode an E3M2 bit pattern to its real value. -/
noncomputable def toReal (x : E3M2) : ℝ :=
  let sign : ℝ := if x.s then -1 else 1
  let mantissa : ℝ := (x.m.val : ℝ) / 4
  if x.e.val = 0 then
    sign * ((2 : ℝ) ^ (-2 : Int)) * mantissa
  else
    sign * (2 : ℝ) ^ ((x.e.val : Int) - bias) * (1 + mantissa)

/-- Maximum positive finite value: `(1 + 3/4) * 2^4 = 28`. -/
noncomputable def maxValue : ℝ := 28

/-- Smallest positive value: `1/16`. -/
noncomputable def minPositive : ℝ := 1 / 16

def isZero (x : E3M2) : Bool := x.e.val = 0 ∧ x.m.val = 0
def isSubnormal (x : E3M2) : Bool := x.e.val = 0 ∧ x.m.val ≠ 0
def isNormal (x : E3M2) : Bool := x.e.val ≠ 0

theorem toReal_pos_zero : toReal ⟨false, 0, 0⟩ = 0 := by
  unfold toReal
  simp

theorem toReal_pos_min : toReal ⟨false, 0, 1⟩ = 1 / 16 := by
  unfold toReal
  norm_num

theorem toReal_pos_one : toReal ⟨false, 3, 0⟩ = 1 := by
  unfold toReal bias
  norm_num

theorem toReal_pos_max : toReal ⟨false, 7, 3⟩ = 28 := by
  unfold toReal bias
  norm_num

/-- Pack to 6 bits.  Bit layout: `s e₂ e₁ e₀ m₁ m₀`. -/
def toBits (x : E3M2) : BitVec 6 :=
  BitVec.ofBool x.s ++ BitVec.ofNat 3 x.e.val ++ BitVec.ofNat 2 x.m.val

/-- Decode from 6 bits. -/
def fromBits (b : BitVec 6) : E3M2 where
  s := b.getLsbD 5
  e := ⟨(b.toNat >>> 2) &&& 0x7, by
    have : (b.toNat >>> 2) &&& 0x7 ≤ 0x7 := Nat.and_le_right
    omega⟩
  m := ⟨b.toNat &&& 0x3, by
    have : b.toNat &&& 0x3 ≤ 0x3 := Nat.and_le_right
    omega⟩

end E3M2

end FP6
end LowFloat
