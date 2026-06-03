import Mathlib.Data.Real.Basic
import Mathlib.Data.BitVec
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.NormNum

/-! # PTX UE4M3

NVIDIA PTX lists `ue4m3` as a 7-bit unsigned floating-point format:

  * 4 exponent bits, 3 mantissa bits, no sign bit.
  * No infinity.
  * NaN is the single all-ones payload `0x7f`.
  * Values are stored in an 8-bit register lane with the MSB padded.

This module formalizes the 7-bit payload.  Packing into an 8-bit lane
is just zero-extension by users of the format.
-/

namespace LowFloat
namespace PTX

/-- Unsigned E4M3 payload: 4 exponent bits + 3 mantissa bits. -/
structure UE4M3 where
  e : Fin 16
  m : Fin 8
  deriving DecidableEq, Fintype, Repr

namespace UE4M3

instance : Inhabited UE4M3 := ⟨⟨7, 0⟩⟩

/-- Bias matching OCP E4M3. -/
def bias : Int := 7

def zero : UE4M3 := ⟨0, 0⟩
def one : UE4M3 := ⟨7, 0⟩
def nan : UE4M3 := ⟨15, 7⟩
def maxFinite : UE4M3 := ⟨15, 6⟩

def isNaN (x : UE4M3) : Bool := x.e.val = 15 ∧ x.m.val = 7
def isZero (x : UE4M3) : Bool := x.e.val = 0 ∧ x.m.val = 0
def isSubnormal (x : UE4M3) : Bool := x.e.val = 0 ∧ x.m.val ≠ 0
def isNormal (x : UE4M3) : Bool := x.isNaN = false ∧ x.e.val ≠ 0

noncomputable def finiteValue (x : UE4M3) : ℝ :=
  let mantissa : ℝ := (x.m.val : ℝ) / 8
  if x.e.val = 0 then
    ((2 : ℝ) ^ (-6 : Int)) * mantissa
  else
    ((2 : ℝ) ^ ((x.e.val : Int) - bias)) * (1 + mantissa)

noncomputable def toReal (x : UE4M3) : Option ℝ :=
  if x.isNaN then none else some x.finiteValue

theorem zero_toReal : zero.toReal = some 0 := by
  unfold toReal zero isNaN finiteValue
  norm_num

theorem one_toReal : one.toReal = some 1 := by
  unfold toReal one isNaN finiteValue bias
  norm_num

theorem nan_toReal : nan.toReal = none := by
  unfold toReal nan isNaN
  norm_num

theorem maxFinite_toReal : maxFinite.toReal = some 448 := by
  unfold toReal maxFinite isNaN finiteValue bias
  norm_num

/-- Pack to the 7-bit payload.  Bit layout: `e₃ e₂ e₁ e₀ m₂ m₁ m₀`. -/
def toBits (x : UE4M3) : BitVec 7 :=
  BitVec.ofNat 4 x.e.val ++ BitVec.ofNat 3 x.m.val

/-- Decode from the 7-bit payload. -/
def fromBits (b : BitVec 7) : UE4M3 where
  e := ⟨(b.toNat >>> 3) &&& 0xF, by
    have : (b.toNat >>> 3) &&& 0xF ≤ 0xF := Nat.and_le_right
    omega⟩
  m := ⟨b.toNat &&& 0x7, by
    have : b.toNat &&& 0x7 ≤ 0x7 := Nat.and_le_right
    omega⟩

end UE4M3

end PTX
end LowFloat
