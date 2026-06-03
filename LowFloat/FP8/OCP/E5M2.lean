import Mathlib.Data.Real.Basic
import Mathlib.Data.BitVec
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! # OCP FP8 E5M2

OCP FP8 `E5M2` is the wider-range FP8 format used alongside `E4M3`:

  * 1 sign bit, 5 exponent bits, 2 mantissa bits.
  * Bias = 15.
  * `e = 31, m = 0` encodes ±∞.
  * `e = 31, m ≠ 0` encodes NaN.
  * Maximum positive finite value is `(1 + 3/4) * 2^15 = 57344`.
-/

namespace LowFloat
namespace FP8
namespace OCP

/-- An OCP FP8 E5M2 value: sign + 5-bit exponent + 2-bit mantissa. -/
structure E5M2 where
  s : Bool
  e : Fin 32
  m : Fin 4
  deriving DecidableEq, Fintype, Repr

namespace E5M2

instance : Inhabited E5M2 := ⟨⟨false, 15, 0⟩⟩

def bias : Int := 15

def zero : E5M2 := ⟨false, 0, 0⟩
def one : E5M2 := ⟨false, 15, 0⟩
def posInf : E5M2 := ⟨false, 31, 0⟩
def negInf : E5M2 := ⟨true, 31, 0⟩
def nan : E5M2 := ⟨false, 31, 1⟩
def maxFinite : E5M2 := ⟨false, 30, 3⟩

def isInf (x : E5M2) : Bool := x.e.val = 31 ∧ x.m.val = 0
def isNaN (x : E5M2) : Bool := x.e.val = 31 ∧ x.m.val ≠ 0
def isFinite (x : E5M2) : Bool := x.e.val ≠ 31
def isZero (x : E5M2) : Bool := x.e.val = 0 ∧ x.m.val = 0
def isSubnormal (x : E5M2) : Bool := x.e.val = 0 ∧ x.m.val ≠ 0
def isNormal (x : E5M2) : Bool := x.e.val ≠ 0 ∧ x.e.val ≠ 31

/-- Decode every non-special bit pattern as if it were finite. -/
noncomputable def finiteValue (x : E5M2) : ℝ :=
  let sign : ℝ := if x.s then -1 else 1
  let mantissa : ℝ := (x.m.val : ℝ) / 4
  if x.e.val = 0 then
    sign * ((2 : ℝ) ^ (-14 : Int)) * mantissa
  else
    sign * ((2 : ℝ) ^ ((x.e.val : Int) - bias)) * (1 + mantissa)

/-- Decode E5M2 to a real, with `none` for infinities and NaNs. -/
noncomputable def toReal (x : E5M2) : Option ℝ :=
  if x.isFinite then some x.finiteValue else none

noncomputable def toRealOrZero (x : E5M2) : ℝ :=
  if x.isFinite then x.finiteValue else 0

theorem zero_toReal : zero.toReal = some 0 := by
  unfold toReal zero isFinite finiteValue
  norm_num

theorem one_toReal : one.toReal = some 1 := by
  unfold toReal one isFinite finiteValue bias
  norm_num

theorem posInf_toReal : posInf.toReal = none := by
  unfold toReal posInf isFinite
  norm_num

theorem nan_toReal : nan.toReal = none := by
  unfold toReal nan isFinite
  norm_num

theorem maxFinite_toReal : maxFinite.toReal = some 57344 := by
  unfold toReal maxFinite isFinite finiteValue bias
  norm_num

/-- Pack to 8 bits.  Bit layout: `s e₄ e₃ e₂ e₁ e₀ m₁ m₀`. -/
def toBits (x : E5M2) : BitVec 8 :=
  BitVec.ofBool x.s ++ BitVec.ofNat 5 x.e.val ++ BitVec.ofNat 2 x.m.val

/-- Decode from 8 bits. -/
def fromBits (b : BitVec 8) : E5M2 where
  s := b.getLsbD 7
  e := ⟨(b.toNat >>> 2) &&& 0x1F, by
    have : (b.toNat >>> 2) &&& 0x1F ≤ 0x1F := Nat.and_le_right
    omega⟩
  m := ⟨b.toNat &&& 0x3, by
    have : b.toNat &&& 0x3 ≤ 0x3 := Nat.and_le_right
    omega⟩

end E5M2

end OCP
end FP8
end LowFloat
