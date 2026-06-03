import Mathlib.Data.Real.Basic
import Mathlib.Data.BitVec
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! # E2M3 — 6-bit low-precision scalar

OCP/NVIDIA/AMD `E2M3` is a 6-bit floating-point format:

  * 1 sign bit, 2 exponent bits, 3 mantissa bits.
  * Bias = 1.
  * No infinities and no NaNs; every bit pattern is finite.

It is one of the FP6 formats exposed by AMD CDNA4/HIP and NVIDIA PTX.
Compared with `E3M2`, it trades range for one extra mantissa bit.
-/

namespace LowFloat
namespace FP6

/-- An E2M3 value: sign + 2-bit exponent + 3-bit mantissa. -/
structure E2M3 where
  s : Bool
  e : Fin 4
  m : Fin 8
  deriving DecidableEq, Fintype, Repr

namespace E2M3

instance : Inhabited E2M3 := ⟨⟨false, 0, 0⟩⟩

/-- Bias for E2M3. -/
def bias : Int := 1

/-- Decode an E2M3 bit pattern to its real value. -/
noncomputable def toReal (x : E2M3) : ℝ :=
  let sign : ℝ := if x.s then -1 else 1
  let mantissa : ℝ := (x.m.val : ℝ) / 8
  if x.e.val = 0 then
    sign * mantissa
  else
    sign * (2 : ℝ) ^ ((x.e.val : Int) - bias) * (1 + mantissa)

/-- Maximum positive finite value: `(1 + 7/8) * 2^2 = 7.5`. -/
noncomputable def maxValue : ℝ := 15 / 2

/-- Smallest positive value: `1/8`. -/
noncomputable def minPositive : ℝ := 1 / 8

def isZero (x : E2M3) : Bool := x.e.val = 0 ∧ x.m.val = 0
def isSubnormal (x : E2M3) : Bool := x.e.val = 0 ∧ x.m.val ≠ 0
def isNormal (x : E2M3) : Bool := x.e.val ≠ 0

theorem toReal_pos_zero : toReal ⟨false, 0, 0⟩ = 0 := by
  unfold toReal
  simp

theorem toReal_pos_min : toReal ⟨false, 0, 1⟩ = 1 / 8 := by
  unfold toReal
  norm_num

theorem toReal_pos_one : toReal ⟨false, 1, 0⟩ = 1 := by
  unfold toReal bias
  norm_num

theorem toReal_pos_max : toReal ⟨false, 3, 7⟩ = 15 / 2 := by
  unfold toReal bias
  norm_num

/-- Pack to 6 bits.  Bit layout: `s e₁ e₀ m₂ m₁ m₀`. -/
def toBits (x : E2M3) : BitVec 6 :=
  BitVec.ofBool x.s ++ BitVec.ofNat 2 x.e.val ++ BitVec.ofNat 3 x.m.val

/-- Decode from 6 bits. -/
def fromBits (b : BitVec 6) : E2M3 where
  s := b.getLsbD 5
  e := ⟨(b.toNat >>> 3) &&& 0x3, by
    have : (b.toNat >>> 3) &&& 0x3 ≤ 0x3 := Nat.and_le_right
    omega⟩
  m := ⟨b.toNat &&& 0x7, by
    have : b.toNat &&& 0x7 ≤ 0x7 := Nat.and_le_right
    omega⟩

end E2M3

end FP6
end LowFloat
