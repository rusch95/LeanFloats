import Mathlib.Data.Real.Basic
import Mathlib.Data.BitVec
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! # AMD FP8 FNUZ formats

AMD CDNA3/MI300 exposes FP8 FNUZ formats in HIP:

  * `E4M3FNUZ`: 1 sign bit, 4 exponent bits, 3 mantissa bits, bias 8.
  * `E5M2FNUZ`: 1 sign bit, 5 exponent bits, 2 mantissa bits, bias 16.

FNUZ means "finite and NaN only":

  * There are no infinities.
  * There is no signed zero.
  * The bit pattern with sign bit set and all exponent/mantissa bits
    clear is NaN (`0x80`).
  * The all-zero bit pattern is the only zero.

This differs from OCP FP8, which CDNA4/MI350 uses instead.
-/

namespace LowFloat
namespace FP8
namespace AMD

/-! ## E4M3 FNUZ -/

structure E4M3FNUZ where
  s : Bool
  e : Fin 16
  m : Fin 8
  deriving DecidableEq, Fintype, Repr

namespace E4M3FNUZ

instance : Inhabited E4M3FNUZ := ⟨⟨false, 8, 0⟩⟩

def bias : Int := 8

def zero : E4M3FNUZ := ⟨false, 0, 0⟩
def one : E4M3FNUZ := ⟨false, 8, 0⟩
def nan : E4M3FNUZ := ⟨true, 0, 0⟩
def maxFinite : E4M3FNUZ := ⟨false, 15, 7⟩

def isNaN (x : E4M3FNUZ) : Bool := x.s = true ∧ x.e.val = 0 ∧ x.m.val = 0
def isZero (x : E4M3FNUZ) : Bool := x.s = false ∧ x.e.val = 0 ∧ x.m.val = 0
def isSubnormal (x : E4M3FNUZ) : Bool := x.e.val = 0 ∧ x.m.val ≠ 0
def isNormal (x : E4M3FNUZ) : Bool := x.e.val ≠ 0

noncomputable def finiteValue (x : E4M3FNUZ) : ℝ :=
  let sign : ℝ := if x.s then -1 else 1
  let mantissa : ℝ := (x.m.val : ℝ) / 8
  if x.e.val = 0 then
    sign * ((2 : ℝ) ^ (-7 : Int)) * mantissa
  else
    sign * ((2 : ℝ) ^ ((x.e.val : Int) - bias)) * (1 + mantissa)

noncomputable def toReal (x : E4M3FNUZ) : Option ℝ :=
  if x.isNaN then none else some x.finiteValue

noncomputable def toRealOrZero (x : E4M3FNUZ) : ℝ :=
  if x.isNaN then 0 else x.finiteValue

theorem zero_toReal : zero.toReal = some 0 := by
  unfold toReal zero isNaN finiteValue
  norm_num

theorem one_toReal : one.toReal = some 1 := by
  unfold toReal one isNaN finiteValue bias
  norm_num

theorem nan_toReal : nan.toReal = none := by
  unfold toReal nan isNaN
  norm_num

theorem maxFinite_toReal : maxFinite.toReal = some 240 := by
  unfold toReal maxFinite isNaN finiteValue bias
  norm_num

def toBits (x : E4M3FNUZ) : BitVec 8 :=
  BitVec.ofBool x.s ++ BitVec.ofNat 4 x.e.val ++ BitVec.ofNat 3 x.m.val

def fromBits (b : BitVec 8) : E4M3FNUZ where
  s := b.getLsbD 7
  e := ⟨(b.toNat >>> 3) &&& 0xF, by
    have : (b.toNat >>> 3) &&& 0xF ≤ 0xF := Nat.and_le_right
    omega⟩
  m := ⟨b.toNat &&& 0x7, by
    have : b.toNat &&& 0x7 ≤ 0x7 := Nat.and_le_right
    omega⟩

end E4M3FNUZ

/-! ## E5M2 FNUZ -/

structure E5M2FNUZ where
  s : Bool
  e : Fin 32
  m : Fin 4
  deriving DecidableEq, Fintype, Repr

namespace E5M2FNUZ

instance : Inhabited E5M2FNUZ := ⟨⟨false, 16, 0⟩⟩

def bias : Int := 16

def zero : E5M2FNUZ := ⟨false, 0, 0⟩
def one : E5M2FNUZ := ⟨false, 16, 0⟩
def nan : E5M2FNUZ := ⟨true, 0, 0⟩
def maxFinite : E5M2FNUZ := ⟨false, 31, 3⟩

def isNaN (x : E5M2FNUZ) : Bool := x.s = true ∧ x.e.val = 0 ∧ x.m.val = 0
def isZero (x : E5M2FNUZ) : Bool := x.s = false ∧ x.e.val = 0 ∧ x.m.val = 0
def isSubnormal (x : E5M2FNUZ) : Bool := x.e.val = 0 ∧ x.m.val ≠ 0
def isNormal (x : E5M2FNUZ) : Bool := x.e.val ≠ 0

noncomputable def finiteValue (x : E5M2FNUZ) : ℝ :=
  let sign : ℝ := if x.s then -1 else 1
  let mantissa : ℝ := (x.m.val : ℝ) / 4
  if x.e.val = 0 then
    sign * ((2 : ℝ) ^ (-15 : Int)) * mantissa
  else
    sign * ((2 : ℝ) ^ ((x.e.val : Int) - bias)) * (1 + mantissa)

noncomputable def toReal (x : E5M2FNUZ) : Option ℝ :=
  if x.isNaN then none else some x.finiteValue

noncomputable def toRealOrZero (x : E5M2FNUZ) : ℝ :=
  if x.isNaN then 0 else x.finiteValue

theorem zero_toReal : zero.toReal = some 0 := by
  unfold toReal zero isNaN finiteValue
  norm_num

theorem one_toReal : one.toReal = some 1 := by
  unfold toReal one isNaN finiteValue bias
  norm_num

theorem nan_toReal : nan.toReal = none := by
  unfold toReal nan isNaN
  norm_num

theorem maxFinite_toReal : maxFinite.toReal = some 57344 := by
  unfold toReal maxFinite isNaN finiteValue bias
  norm_num

def toBits (x : E5M2FNUZ) : BitVec 8 :=
  BitVec.ofBool x.s ++ BitVec.ofNat 5 x.e.val ++ BitVec.ofNat 2 x.m.val

def fromBits (b : BitVec 8) : E5M2FNUZ where
  s := b.getLsbD 7
  e := ⟨(b.toNat >>> 2) &&& 0x1F, by
    have : (b.toNat >>> 2) &&& 0x1F ≤ 0x1F := Nat.and_le_right
    omega⟩
  m := ⟨b.toNat &&& 0x3, by
    have : b.toNat &&& 0x3 ≤ 0x3 := Nat.and_le_right
    omega⟩

end E5M2FNUZ

end AMD
end FP8
end LowFloat
