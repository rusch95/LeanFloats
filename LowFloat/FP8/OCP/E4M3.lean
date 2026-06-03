import Mathlib.Data.Real.Basic
import Mathlib.Data.BitVec
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! # OCP FP8 E4M3

OCP FP8 `E4M3` is the finite-and-NaN FP8 format used by NVIDIA,
AMD CDNA4, and OCP-compatible software stacks:

  * 1 sign bit, 4 exponent bits, 3 mantissa bits.
  * Bias = 7.
  * No infinities.
  * The all-ones exponent with all-ones mantissa is NaN.
  * Other all-ones exponent payloads are finite, so the maximum
    positive finite value is `(1 + 6/8) * 2^8 = 448`.
-/

namespace LowFloat
namespace FP8
namespace OCP

/-- An FP8 E4M3 value: sign + 4-bit exponent + 3-bit mantissa. -/
structure E4M3 where
  s : Bool
  e : Fin 16
  m : Fin 8
  deriving DecidableEq, Fintype, Repr

namespace E4M3

instance : Inhabited E4M3 := ⟨⟨false, 7, 0⟩⟩

/-- Bias for E4M3. -/
def bias : Int := 7

/-- The single mantissa payload reserved for NaN when `e = 15`. -/
def nanMantissa : Fin 8 := 7

/-- Positive zero. -/
def zero : E4M3 := ⟨false, 0, 0⟩

/-- The scale value `1`. -/
def one : E4M3 := ⟨false, 7, 0⟩

/-- A quiet NaN representative. -/
def nan : E4M3 := ⟨false, 15, nanMantissa⟩

/-- Largest positive finite E4M3 value: `448`. -/
def maxFinite : E4M3 := ⟨false, 15, 6⟩

/-- E4M3 reserves only exponent `15`, mantissa `7` as NaN. -/
def isNaN (x : E4M3) : Bool := x.e.val = 15 ∧ x.m.val = 7

/-- `e = 0, m = 0`: signed zero. -/
def isZero (x : E4M3) : Bool := x.e.val = 0 ∧ x.m.val = 0

/-- `e = 0, m ≠ 0`: subnormal. -/
def isSubnormal (x : E4M3) : Bool := x.e.val = 0 ∧ x.m.val ≠ 0

/-- Finite, nonzero exponent.  This includes finite `e = 15`, `m ≠ 7`. -/
def isNormal (x : E4M3) : Bool := x.isNaN = false ∧ x.e.val ≠ 0

@[simp] theorem isNaN_nan : nan.isNaN = true := by
  unfold isNaN nan nanMantissa
  decide

@[simp] theorem isNaN_one : one.isNaN = false := by
  unfold isNaN one
  decide

@[simp] theorem isNaN_zero : zero.isNaN = false := by
  unfold isNaN zero
  decide

/-- Decode every bit pattern as if it were finite.  `toReal` masks
    this with `none` for NaN. -/
noncomputable def finiteValue (x : E4M3) : ℝ :=
  let sign : ℝ := if x.s then -1 else 1
  let mantissa : ℝ := (x.m.val : ℝ) / 8
  if x.e.val = 0 then
    sign * ((2 : ℝ) ^ (-6 : Int)) * mantissa
  else
    sign * ((2 : ℝ) ^ ((x.e.val : Int) - bias)) * (1 + mantissa)

/-- Decode E4M3 to a real value, with `none` for NaN. -/
noncomputable def toReal (x : E4M3) : Option ℝ :=
  if x.isNaN then none else some x.finiteValue

/-- Real value with `0` as a sentinel for NaN.  Prefer `toReal`
    unless the NaN case has already been discharged. -/
noncomputable def toRealOrZero (x : E4M3) : ℝ :=
  if x.isNaN then 0 else x.finiteValue

theorem zero_toReal : zero.toReal = some 0 := by
  unfold toReal zero isNaN finiteValue
  norm_num

theorem one_toReal : one.toReal = some 1 := by
  unfold toReal one isNaN finiteValue bias
  norm_num

theorem nan_toReal : nan.toReal = none := by
  unfold toReal nan isNaN nanMantissa
  norm_num

theorem maxFinite_toReal : maxFinite.toReal = some 448 := by
  unfold toReal maxFinite isNaN finiteValue bias
  norm_num

/-- Pack to 8 bits.  Bit layout: `s e₃ e₂ e₁ e₀ m₂ m₁ m₀`. -/
def toBits (x : E4M3) : BitVec 8 :=
  BitVec.ofBool x.s ++ BitVec.ofNat 4 x.e.val ++ BitVec.ofNat 3 x.m.val

/-- Decode from 8 bits. -/
def fromBits (b : BitVec 8) : E4M3 where
  s := b.getLsbD 7
  e := ⟨(b.toNat >>> 3) &&& 0xF, by
    have : (b.toNat >>> 3) &&& 0xF ≤ 0xF := Nat.and_le_right
    omega⟩
  m := ⟨b.toNat &&& 0x7, by
    have : b.toNat &&& 0x7 ≤ 0x7 := Nat.and_le_right
    omega⟩

end E4M3

end OCP
end FP8
end LowFloat
