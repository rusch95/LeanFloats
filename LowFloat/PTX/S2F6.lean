import Mathlib.Data.Real.Basic
import Mathlib.Data.BitVec
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.NormNum

/-! # PTX S2F6 fixed-point format

PTX also lists `s2f6`, which is not a floating-point format.  It is
an 8-bit signed fixed-point value with two integer/sign bits and six
fractional bits:

`value = signed_int8(raw) * 2^-6`.

It is included here as adjacent low-precision coverage so readers do
not confuse it with FP6 `E2M3` / `E3M2`.
-/

namespace LowFloat
namespace PTX

/-- Signed 2.6 fixed-point payload. -/
structure S2F6 where
  raw : Fin 256
  deriving DecidableEq, Fintype, Repr

namespace S2F6

instance : Inhabited S2F6 := ⟨⟨0⟩⟩

/-- Interpret the raw byte as signed two's-complement int8. -/
def signedInt (x : S2F6) : Int :=
  if x.raw.val < 128 then (x.raw.val : Int) else (x.raw.val : Int) - 256

/-- Decode as a real fixed-point value. -/
noncomputable def toReal (x : S2F6) : ℝ :=
  (x.signedInt : ℝ) / 64

def zero : S2F6 := ⟨0⟩
def maxPositive : S2F6 := ⟨127⟩
def minNegative : S2F6 := ⟨128⟩

theorem zero_toReal : zero.toReal = 0 := by
  unfold toReal signedInt zero
  norm_num

theorem maxPositive_toReal : maxPositive.toReal = 127 / 64 := by
  unfold toReal signedInt maxPositive
  norm_num

theorem minNegative_toReal : minNegative.toReal = -2 := by
  unfold toReal signedInt minNegative
  norm_num

def toBits (x : S2F6) : BitVec 8 := BitVec.ofNat 8 x.raw.val

def fromBits (b : BitVec 8) : S2F6 := ⟨⟨b.toNat, b.isLt⟩⟩

end S2F6

end PTX
end LowFloat
