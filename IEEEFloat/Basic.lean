import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype

/-! # IEEE 754 binary floating-point — type definition

`IEEEFloat eb mb` is the type of binary IEEE 754 floats with `eb`
exponent bits and `mb` (trailing) mantissa bits.

Encoding follows IEEE 754-2019 §3.4 (binary interchange formats):

  * sign:     1 bit
  * exponent: `eb` bits, biased by `2^(eb-1) - 1`
  * mantissa: `mb` bits (the trailing significand; the leading bit is
              implicit `1` for normals, `0` for subnormals)

The "all-ones" biased exponent value `2^eb - 1` is reserved for NaN
and ±∞; the biased exponent of a `finite` value is therefore carried
as `Fin (2 ^ eb - 1)` so the type cannot encode the reserved pattern.

The single `nan` constructor intentionally erases NaN sign and
payload.  IEEE 754 leaves both implementation-defined, so theorems
at this layer should not depend on them.  A bit-pattern-level
refinement (e.g. `nan (s : Bool) (payload : Fin (2 ^ mb - 1))`)
belongs in a separate module if and when needed (e.g. for `bitcast`
or for the WGSL §15.7 NaN-pattern non-determinism layer).
-/

/-- Strict IEEE 754 binary float at format `(eb, mb)`. -/
inductive IEEEFloat (eb mb : Nat) : Type where
  /-- A NaN.  Sign and payload erased at this layer. -/
  | nan
  /-- ±∞.  `s = false` for `+∞`, `s = true` for `−∞`. -/
  | inf (s : Bool)
  /-- A finite value with sign `s`, biased exponent `e`, trailing mantissa `m`.
      `e = 0, m = 0` is signed zero (`s` distinguishes ±0).
      `e = 0, m ≠ 0` is subnormal.
      `e ≠ 0` is normal. -/
  | finite (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb))
  deriving DecidableEq, Fintype

namespace IEEEFloat

variable {eb mb : Nat}

instance : Inhabited (IEEEFloat eb mb) := ⟨.nan⟩

/-! ## Format constants -/

/-- IEEE bias for an `eb`-bit biased exponent: `2^(eb-1) - 1`.
    f16 → 15, f32 → 127, f64 → 1023. -/
def bias (eb : Nat) : Int := (2 : Int) ^ (eb - 1) - 1

/-- Largest unbiased exponent of a finite value: equal to `bias eb`.
    f32 → 127. -/
def maxExp (eb : Nat) : Int := bias eb

/-- Smallest unbiased exponent of a normal value: `1 - bias`.
    f32 → −126. -/
def minNormalExp (eb : Nat) : Int := 1 - bias eb

/-- Smallest unbiased exponent of any (subnormal) value:
    `minNormalExp eb - mb`.  f32 → −149. -/
def minSubnormalExp (eb mb : Nat) : Int := minNormalExp eb - mb

/-! ## Predicates -/

def isNaN : IEEEFloat eb mb → Bool
  | .nan => true
  | _    => false

def isInf : IEEEFloat eb mb → Bool
  | .inf _ => true
  | _      => false

def isFinite : IEEEFloat eb mb → Bool
  | .finite _ _ _ => true
  | _             => false

/-- Both `+0` and `−0` are zero. -/
def isZero : IEEEFloat eb mb → Bool
  | .finite _ e m => e.val == 0 && m.val == 0
  | _             => false

/-- Finite, biased exponent zero, mantissa nonzero. -/
def isSubnormal : IEEEFloat eb mb → Bool
  | .finite _ e m => e.val == 0 && m.val != 0
  | _             => false

/-- Finite, biased exponent ≥ 1. -/
def isNormal : IEEEFloat eb mb → Bool
  | .finite _ e _ => e.val != 0
  | _             => false

/-- Sign bit.  Under our single-NaN encoding NaN's sign is unobservable;
    we return `false`. -/
def signBit : IEEEFloat eb mb → Bool
  | .nan          => false
  | .inf s        => s
  | .finite s _ _ => s

/-- Mantissa LSB as `Nat` (`0` or `1`).  Returns `0` for nonfinite. -/
def mantissaLSB : IEEEFloat eb mb → Nat
  | .finite _ _ m => m.val % 2
  | _             => 0

@[simp] theorem mantissaLSB_finite (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    mantissaLSB (.finite s e m : IEEEFloat eb mb) = m.val % 2 := rfl

@[simp] theorem mantissaLSB_nan : mantissaLSB (.nan : IEEEFloat eb mb) = 0 := rfl

@[simp] theorem mantissaLSB_inf (s : Bool) :
    mantissaLSB (.inf s : IEEEFloat eb mb) = 0 := rfl

/-! ## Negation

    Sign-bit flip.  Total — does not round, does not depend on the
    operand's value.  Defined here (not in `Arith`) because it is
    not a rounded operation. -/

def neg : IEEEFloat eb mb → IEEEFloat eb mb
  | .nan          => .nan
  | .inf s        => .inf (!s)
  | .finite s e m => .finite (!s) e m

instance : Neg (IEEEFloat eb mb) := ⟨neg⟩

@[simp] theorem neg_nan : neg (eb := eb) (mb := mb) .nan = .nan := rfl
@[simp] theorem neg_inf (s : Bool) :
    neg (eb := eb) (mb := mb) (.inf s) = .inf (!s) := rfl
@[simp] theorem neg_finite (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    neg (.finite s e m) = .finite (!s) e m := rfl

theorem neg_neg (x : IEEEFloat eb mb) : neg (neg x) = x := by
  cases x with
  | nan          => rfl
  | inf s        => simp [neg]
  | finite s e m => simp [neg]

end IEEEFloat
