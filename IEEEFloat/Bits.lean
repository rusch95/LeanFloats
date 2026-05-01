import Mathlib.Data.BitVec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import IEEEFloat.Basic

/-! # Bit-pattern interchange — `IEEEFloat eb mb ↔ BitVec (1+eb+mb)`

IEEE 754-2019 §3.4 specifies an interchange bit-pattern for each
binary format: a sign bit, a biased exponent field, and a trailing
mantissa field, packed (sign at MSB) into `1+eb+mb` bits.  This
module realises that encoding.

The `.nan` constructor of `IEEEFloat` deliberately erases NaN sign
and payload, so the bit-pattern map is *many-to-one* on NaN and only
a section / surjection — `toBits` picks a canonical quiet NaN
(`sign=0, exp=all-ones, mantissa=10…0`) and `fromBits` collapses
*every* nonzero-mantissa all-ones-exponent pattern to `.nan`.

The two key bijection theorems are:
  *  `fromBits_toBits_finite`: round-trip on every finite encoding.
  *  `fromBits_toBits_inf` / `fromBits_toBits_nan`: round-trip on
     `±∞` / canonical NaN.

A faithful `toBits ∘ fromBits = id` requires `1 ≤ mb` (otherwise
`.nan` cannot be distinguished from `.inf false` at the bit level).
None of the real interchange formats (`Binary16`–`Binary64`,
`BFloat16`) hit this corner.
-/

namespace IEEEFloat

variable {eb mb : Nat}

/-- IEEE 754 bit-pattern width: sign (1) + biased exponent (`eb`) +
    trailing mantissa (`mb`). -/
abbrev BitPattern (eb mb : Nat) : Type := BitVec (1 + eb + mb)

/-! ## Nat-arithmetic helper

Three-field encoding `s * 2^(eb+mb) + e * 2^mb + m` is the underlying
nat for every bit pattern this module produces.  We push everything
to that form so `toBits`, the field projections, and the round-trip
proofs can all reuse the same Nat-level identity. -/

/-- `a * 2^n` and `b` have disjoint bit ranges when `b < 2^n`, so
    bitwise-or coincides with addition. -/
private theorem mul_two_pow_or_eq_add (a b n : Nat) (h : b < 2 ^ n) :
    a * 2 ^ n ||| b = a * 2 ^ n + b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.mul_comm a (2 ^ n)]
  rw [Nat.testBit_two_pow_mul_add a h]
  by_cases hj : j < n
  · have h1 : (2 ^ n * a).testBit j = false := by
      rw [Nat.mul_comm, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
      simp; omega
    simp [h1, hj]
  · push_neg at hj
    have h2 : (2 : Nat) ^ n ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj
    have hb_zero : b.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le h h2)
    rw [hb_zero, Nat.mul_comm, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
    simp [hj]

/-- The closed-form `Nat` value of a three-way bit append, when each
    field's `Nat` value is in range. -/
private theorem toNat_triple_append
    (s : Bool) (eVal mVal : Nat) (he : eVal < 2 ^ eb) (hm : mVal < 2 ^ mb) :
    ((BitVec.ofBool s ++ BitVec.ofNat eb eVal ++ BitVec.ofNat mb mVal :
        BitPattern eb mb)).toNat
      = s.toNat * 2 ^ (eb + mb) + eVal * 2 ^ mb + mVal := by
  rw [BitVec.toNat_append, BitVec.toNat_append]
  rw [BitVec.toNat_ofBool, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hm]
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  rw [mul_two_pow_or_eq_add _ _ _ he, mul_two_pow_or_eq_add _ _ _ hm]
  rw [pow_add]
  ring

/-! ## Encoding (`toBits`) -/

/-- Canonical quiet-NaN trailing-mantissa pattern: MSB set, rest zero.
    For `mb = 0` this is the zero bitvector — `IEEEFloat eb 0`'s
    `.nan` then has the same bit pattern as `.inf false` (the
    degenerate format has no faithful encoding). -/
def qnanMantissa (mb : Nat) : BitVec mb :=
  BitVec.ofNat mb (2 ^ (mb - 1))

/-- Encode an `IEEEFloat` to its IEEE 754 bit pattern. -/
def toBits : IEEEFloat eb mb → BitPattern eb mb
  | .nan          =>
      BitVec.ofBool false ++ BitVec.ofNat eb (2 ^ eb - 1) ++ qnanMantissa mb
  | .inf s        =>
      BitVec.ofBool s ++ BitVec.ofNat eb (2 ^ eb - 1) ++ BitVec.ofNat mb 0
  | .finite s e m =>
      BitVec.ofBool s ++ BitVec.ofNat eb e.val ++ BitVec.ofNat mb m.val

/-! ## Field projections -/

/-- Sign bit (the MSB of the bit pattern). -/
def signBitOf (b : BitPattern eb mb) : Bool :=
  b.getLsbD (eb + mb)

/-- Biased exponent field, as a `Nat` (always `< 2^eb`). -/
def expFieldNat (b : BitPattern eb mb) : Nat :=
  (b.extractLsb' mb eb).toNat

/-- Trailing mantissa field, as a `Nat` (always `< 2^mb`). -/
def mantissaFieldNat (b : BitPattern eb mb) : Nat :=
  (b.extractLsb' 0 mb).toNat

theorem expFieldNat_lt (b : BitPattern eb mb) :
    expFieldNat b < 2 ^ eb := (b.extractLsb' mb eb).isLt

theorem mantissaFieldNat_lt (b : BitPattern eb mb) :
    mantissaFieldNat b < 2 ^ mb := (b.extractLsb' 0 mb).isLt

/-- `extractLsb' k l b` is the slice of `b.toNat` occupying bits `[k, k+l)`. -/
private theorem extractLsb'_toNat {n : Nat} (b : BitVec n) (k l : Nat) :
    (b.extractLsb' k l).toNat = b.toNat / 2 ^ k % 2 ^ l := by
  unfold BitVec.extractLsb'
  rw [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]

/-! ## Field projections of `toBits` (the round-trip kernel)

These three lemmas plus the `2^eb - 1` exponent test are everything
the round-trip proofs need. -/

/-- Bit `i` of a `BitVec n` is the `i`-th `testBit` of its `Nat` value. -/
private theorem getLsbD_eq_testBit {n : Nat} (b : BitVec n) (i : Nat) :
    b.getLsbD i = b.toNat.testBit i := (BitVec.testBit_toNat b).symm

theorem signBitOf_toBits_finite (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    signBitOf (toBits (eb := eb) (mb := mb) (.finite s e m)) = s := by
  unfold signBitOf toBits
  rw [getLsbD_eq_testBit]
  have h_e : e.val < 2 ^ eb := lt_of_lt_of_le e.isLt (Nat.sub_le _ _)
  rw [toNat_triple_append s e.val m.val h_e m.isLt]
  have h_low : e.val * 2 ^ mb + m.val < 2 ^ (eb + mb) := by
    rw [pow_add]
    have h_e_succ : e.val + 1 ≤ 2 ^ eb := by have := e.isLt; omega
    have h_step : e.val * 2 ^ mb + m.val < (e.val + 1) * 2 ^ mb := by
      have h_eq : (e.val + 1) * 2 ^ mb = e.val * 2 ^ mb + 2 ^ mb := by ring
      rw [h_eq]; have := m.isLt; omega
    have h_le : (e.val + 1) * 2 ^ mb ≤ 2 ^ eb * 2 ^ mb :=
      Nat.mul_le_mul_right _ h_e_succ
    omega
  -- Reshape: s.toNat * 2^(eb+mb) + (e.val * 2^mb + m.val), then rotate to
  -- 2^(eb+mb) * s.toNat + ... so Nat.testBit_two_pow_mul_add applies.
  rw [show s.toNat * 2 ^ (eb + mb) + e.val * 2 ^ mb + m.val
        = 2 ^ (eb + mb) * s.toNat + (e.val * 2 ^ mb + m.val) from by ring]
  rw [Nat.testBit_two_pow_mul_add s.toNat h_low]
  simp
  rcases s with _ | _ <;> rfl

theorem expFieldNat_toBits_finite (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    expFieldNat (toBits (eb := eb) (mb := mb) (.finite s e m)) = e.val := by
  unfold expFieldNat toBits
  rw [extractLsb'_toNat]
  have h_e : e.val < 2 ^ eb := lt_of_lt_of_le e.isLt (Nat.sub_le _ _)
  rw [toNat_triple_append s e.val m.val h_e m.isLt]
  have h_two_pow_mb_pos : 0 < 2 ^ mb := Nat.pos_of_ne_zero (by
    intro h; have := @Nat.one_le_two_pow mb; omega)
  -- Pull the 2^mb out: stuff * 2^mb + m
  rw [show s.toNat * 2 ^ (eb + mb) + e.val * 2 ^ mb + m.val
        = m.val + (s.toNat * 2 ^ eb + e.val) * 2 ^ mb from by rw [pow_add]; ring]
  rw [Nat.add_mul_div_right _ _ h_two_pow_mb_pos]
  rw [Nat.div_eq_of_lt m.isLt, Nat.zero_add]
  -- Goal: (s.toNat * 2^eb + e.val) % 2^eb = e.val
  rw [show s.toNat * 2 ^ eb + e.val = e.val + 2 ^ eb * s.toNat from by ring]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt h_e

theorem mantissaFieldNat_toBits_finite (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    mantissaFieldNat (toBits (eb := eb) (mb := mb) (.finite s e m)) = m.val := by
  unfold mantissaFieldNat toBits
  rw [extractLsb'_toNat]
  have h_e : e.val < 2 ^ eb := lt_of_lt_of_le e.isLt (Nat.sub_le _ _)
  rw [toNat_triple_append s e.val m.val h_e m.isLt]
  rw [pow_zero, Nat.div_one]
  -- Goal: (s.toNat * 2^(eb+mb) + e.val * 2^mb + m.val) % 2^mb = m.val
  rw [show s.toNat * 2 ^ (eb + mb) + e.val * 2 ^ mb + m.val
        = m.val + 2 ^ mb * (s.toNat * 2 ^ eb + e.val) from by rw [pow_add]; ring]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt m.isLt

/-! ## Field projections of `toBits` for `±∞` and the canonical NaN -/

theorem signBitOf_toBits_inf (s : Bool) :
    signBitOf (toBits (eb := eb) (mb := mb) (.inf s)) = s := by
  unfold signBitOf toBits
  rw [getLsbD_eq_testBit]
  have h_e : 2 ^ eb - 1 < 2 ^ eb := by
    have : 1 ≤ 2 ^ eb := Nat.one_le_two_pow; omega
  have h_m : (0 : Nat) < 2 ^ mb := Nat.one_le_two_pow
  rw [toNat_triple_append s (2 ^ eb - 1) 0 h_e h_m]
  have h_low : (2 ^ eb - 1) * 2 ^ mb + 0 < 2 ^ (eb + mb) := by
    rw [pow_add, Nat.add_zero]
    exact (Nat.mul_lt_mul_right Nat.one_le_two_pow).mpr h_e
  rw [show s.toNat * 2 ^ (eb + mb) + (2 ^ eb - 1) * 2 ^ mb + 0
        = 2 ^ (eb + mb) * s.toNat + ((2 ^ eb - 1) * 2 ^ mb + 0) from by ring]
  rw [Nat.testBit_two_pow_mul_add s.toNat h_low]
  simp
  rcases s with _ | _ <;> rfl

theorem expFieldNat_toBits_inf (s : Bool) :
    expFieldNat (toBits (eb := eb) (mb := mb) (.inf s)) = 2 ^ eb - 1 := by
  unfold expFieldNat toBits
  rw [extractLsb'_toNat]
  have h_e : 2 ^ eb - 1 < 2 ^ eb := by
    have : 1 ≤ 2 ^ eb := Nat.one_le_two_pow; omega
  have h_m : (0 : Nat) < 2 ^ mb := Nat.one_le_two_pow
  rw [toNat_triple_append s (2 ^ eb - 1) 0 h_e h_m]
  have h_two_pow_mb_pos : 0 < 2 ^ mb := Nat.one_le_two_pow
  rw [show s.toNat * 2 ^ (eb + mb) + (2 ^ eb - 1) * 2 ^ mb + 0
        = 0 + (s.toNat * 2 ^ eb + (2 ^ eb - 1)) * 2 ^ mb from by rw [pow_add]; ring]
  rw [Nat.add_mul_div_right _ _ h_two_pow_mb_pos]
  rw [Nat.zero_div, Nat.zero_add]
  rw [show s.toNat * 2 ^ eb + (2 ^ eb - 1) = (2 ^ eb - 1) + 2 ^ eb * s.toNat from by ring]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt h_e

theorem mantissaFieldNat_toBits_inf (s : Bool) :
    mantissaFieldNat (toBits (eb := eb) (mb := mb) (.inf s)) = 0 := by
  unfold mantissaFieldNat toBits
  rw [extractLsb'_toNat]
  have h_e : 2 ^ eb - 1 < 2 ^ eb := by
    have : 1 ≤ 2 ^ eb := Nat.one_le_two_pow; omega
  have h_m : (0 : Nat) < 2 ^ mb := Nat.one_le_two_pow
  rw [toNat_triple_append s (2 ^ eb - 1) 0 h_e h_m]
  rw [pow_zero, Nat.div_one]
  rw [show s.toNat * 2 ^ (eb + mb) + (2 ^ eb - 1) * 2 ^ mb + 0
        = 0 + 2 ^ mb * (s.toNat * 2 ^ eb + (2 ^ eb - 1)) from by rw [pow_add]; ring]
  rw [Nat.add_mul_mod_self_left]
  rfl

theorem signBitOf_toBits_nan (hmb : 1 ≤ mb) :
    signBitOf (toBits (eb := eb) (mb := mb) .nan) = false := by
  unfold signBitOf toBits qnanMantissa
  rw [getLsbD_eq_testBit]
  have h_e : 2 ^ eb - 1 < 2 ^ eb := by
    have : 1 ≤ 2 ^ eb := Nat.one_le_two_pow; omega
  have h_m : 2 ^ (mb - 1) < 2 ^ mb :=
    Nat.pow_lt_pow_right (by norm_num) (by omega : mb - 1 < mb)
  rw [toNat_triple_append false (2 ^ eb - 1) (2 ^ (mb - 1)) h_e h_m]
  have h_low : (2 ^ eb - 1) * 2 ^ mb + 2 ^ (mb - 1) < 2 ^ (eb + mb) := by
    rw [pow_add]
    have h_e_succ : 2 ^ eb - 1 + 1 ≤ 2 ^ eb := by
      have : 1 ≤ 2 ^ eb := Nat.one_le_two_pow; omega
    have h1 : (2 ^ eb - 1) * 2 ^ mb + 2 ^ (mb - 1)
              < (2 ^ eb - 1) * 2 ^ mb + 2 ^ mb := by
      have : 2 ^ (mb - 1) < 2 ^ mb := h_m; omega
    have h2 : (2 ^ eb - 1) * 2 ^ mb + 2 ^ mb = (2 ^ eb - 1 + 1) * 2 ^ mb := by ring
    have h3 : (2 ^ eb - 1 + 1) * 2 ^ mb ≤ 2 ^ eb * 2 ^ mb :=
      Nat.mul_le_mul_right _ h_e_succ
    omega
  rw [show false.toNat * 2 ^ (eb + mb) + (2 ^ eb - 1) * 2 ^ mb + 2 ^ (mb - 1)
        = 2 ^ (eb + mb) * false.toNat
            + ((2 ^ eb - 1) * 2 ^ mb + 2 ^ (mb - 1)) from by ring]
  rw [Nat.testBit_two_pow_mul_add false.toNat h_low]
  simp

theorem expFieldNat_toBits_nan (hmb : 1 ≤ mb) :
    expFieldNat (toBits (eb := eb) (mb := mb) .nan) = 2 ^ eb - 1 := by
  unfold expFieldNat toBits qnanMantissa
  rw [extractLsb'_toNat]
  have h_e : 2 ^ eb - 1 < 2 ^ eb := by
    have : 1 ≤ 2 ^ eb := Nat.one_le_two_pow; omega
  have h_m : 2 ^ (mb - 1) < 2 ^ mb :=
    Nat.pow_lt_pow_right (by norm_num) (by omega : mb - 1 < mb)
  rw [toNat_triple_append false (2 ^ eb - 1) (2 ^ (mb - 1)) h_e h_m]
  have h_two_pow_mb_pos : 0 < 2 ^ mb := Nat.one_le_two_pow
  rw [show false.toNat * 2 ^ (eb + mb) + (2 ^ eb - 1) * 2 ^ mb + 2 ^ (mb - 1)
        = 2 ^ (mb - 1) + (false.toNat * 2 ^ eb + (2 ^ eb - 1)) * 2 ^ mb from by
      rw [pow_add]; ring]
  rw [Nat.add_mul_div_right _ _ h_two_pow_mb_pos]
  rw [Nat.div_eq_of_lt h_m, Nat.zero_add]
  simp [Bool.toNat, Nat.mod_eq_of_lt h_e]

/-- The canonical NaN's mantissa field equals `2 ^ (mb - 1)`.  In
    particular it is *nonzero* whenever `1 ≤ mb`, ensuring `.nan` and
    `.inf _` produce distinct bit patterns. -/
theorem mantissaFieldNat_toBits_nan (hmb : 1 ≤ mb) :
    mantissaFieldNat (toBits (eb := eb) (mb := mb) .nan) = 2 ^ (mb - 1) := by
  unfold mantissaFieldNat toBits qnanMantissa
  rw [extractLsb'_toNat]
  have h_e : 2 ^ eb - 1 < 2 ^ eb := by
    have : 1 ≤ 2 ^ eb := Nat.one_le_two_pow; omega
  have h_m : 2 ^ (mb - 1) < 2 ^ mb :=
    Nat.pow_lt_pow_right (by norm_num) (by omega : mb - 1 < mb)
  rw [toNat_triple_append false (2 ^ eb - 1) (2 ^ (mb - 1)) h_e h_m]
  rw [pow_zero, Nat.div_one]
  rw [show false.toNat * 2 ^ (eb + mb) + (2 ^ eb - 1) * 2 ^ mb + 2 ^ (mb - 1)
        = 2 ^ (mb - 1) + 2 ^ mb * (false.toNat * 2 ^ eb + (2 ^ eb - 1)) from by
      rw [pow_add]; ring]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt h_m

/-! ## Decoding (`fromBits`) -/

/-- Decode a bit pattern to an `IEEEFloat`.  All bit patterns with
    all-ones exponent and nonzero mantissa collapse to `.nan` (the
    sign and payload are dropped), reflecting the strict-IEEE
    convention that NaN sign/payload is implementation-defined. -/
def fromBits (b : BitPattern eb mb) : IEEEFloat eb mb :=
  if h_e : expFieldNat b = 2 ^ eb - 1 then
    if mantissaFieldNat b = 0 then .inf (signBitOf b) else .nan
  else
    .finite (signBitOf b)
      ⟨expFieldNat b, by
        have h1 := expFieldNat_lt (b := b)
        have h2 : 1 ≤ 2 ^ eb := Nat.one_le_two_pow
        omega⟩
      ⟨mantissaFieldNat b, mantissaFieldNat_lt (b := b)⟩

/-! ## Round-trip: `fromBits ∘ toBits = id` -/

theorem fromBits_toBits_finite (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    fromBits (toBits (.finite s e m)) = .finite s e m := by
  unfold fromBits
  have h_e_eq := expFieldNat_toBits_finite s e m
  have h_m_eq := mantissaFieldNat_toBits_finite s e m
  have h_s_eq := signBitOf_toBits_finite s e m
  have h_ne : expFieldNat (toBits (.finite s e m)) ≠ 2 ^ eb - 1 := by
    rw [h_e_eq]
    intro h_eq
    have := e.isLt
    omega
  rw [dif_neg h_ne]
  congr 1
  · exact Fin.ext h_e_eq
  · exact Fin.ext h_m_eq

theorem fromBits_toBits_inf (s : Bool) :
    fromBits (toBits (eb := eb) (mb := mb) (.inf s)) = .inf s := by
  unfold fromBits
  rw [dif_pos (expFieldNat_toBits_inf s), if_pos (mantissaFieldNat_toBits_inf s),
      signBitOf_toBits_inf]

theorem fromBits_toBits_nan (hmb : 1 ≤ mb) :
    fromBits (toBits (eb := eb) (mb := mb) .nan) = .nan := by
  unfold fromBits
  have h_m_eq := mantissaFieldNat_toBits_nan (eb := eb) hmb
  have h_m_ne : mantissaFieldNat (toBits (eb := eb) (mb := mb) .nan) ≠ 0 := by
    rw [h_m_eq]; positivity
  rw [dif_pos (expFieldNat_toBits_nan (eb := eb) hmb), if_neg h_m_ne]

/-- The round-trip equation, branching on which constructor `x` is.
    Holds for every constructor under `1 ≤ mb`; without the guard,
    the `.nan` case fails for `mb = 0` (where no NaN bit pattern
    exists). -/
theorem fromBits_toBits (hmb : 1 ≤ mb) (x : IEEEFloat eb mb) :
    fromBits (toBits x) = x := by
  cases x with
  | nan          => exact fromBits_toBits_nan hmb
  | inf s        => exact fromBits_toBits_inf s
  | finite s e m => exact fromBits_toBits_finite s e m

/-- `toBits` is injective when `1 ≤ mb`. -/
theorem toBits_injective (hmb : 1 ≤ mb) :
    Function.Injective (toBits (eb := eb) (mb := mb)) := by
  intro x y h
  have hx := fromBits_toBits hmb x
  have hy := fromBits_toBits hmb y
  rw [← hx, ← hy, h]

end IEEEFloat
