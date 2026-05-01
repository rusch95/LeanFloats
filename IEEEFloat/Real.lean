import Mathlib.Data.Real.Basic
import IEEEFloat.Basic

/-! # Real-valued interpretation

`toReal` maps an `IEEEFloat eb mb` to its mathematical value in `ℝ`,
returning `none` for NaN and ±∞ (neither has a finite real value).
The point of this layer is to translate IEEE 754 statements into
plain real-arithmetic statements so that the existing `Mathlib`
real-analysis API can carry the proofs.

The `finiteValue` helper exposes the decoding of a `finite`
encoding directly, without going through `Option`, so theorems
about specific bit patterns can avoid an `Option.some` peel.

This module is `noncomputable` — `Real` is.  A computable shim
backed by host `Float` lives separately (planned, `IEEEFloat.Host`).
-/

namespace IEEEFloat

variable {eb mb : Nat}

/-- Real-valued interpretation of a `finite` encoding's fields.

* Normal (`e ≠ 0`):     `(-1)^s · 2^(e - bias) · (1 + m / 2^mb)`
* Subnormal (`e = 0`):  `(-1)^s · 2^(1 - bias) · (m / 2^mb)`

The two branches share the same numerical value at `e = 1, m = 0`
(smallest normal) — by construction, since the subnormal formula
with `m = 2^mb` would equal the normal formula with `e = 1, m = 0`.
-/
noncomputable def finiteValue
    (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) : ℝ :=
  let sign : ℝ := if s then -1 else 1
  let mantissa : ℝ := (m.val : ℝ) / (2 : ℝ) ^ mb
  if e.val = 0 then
    sign * ((2 : ℝ) ^ minNormalExp eb) * mantissa
  else
    sign * ((2 : ℝ) ^ ((e.val : Int) - bias eb)) * (1 + mantissa)

/-- Real-value projection.  `none` for NaN and ±∞ (no finite real
    value); `some r` for finite encodings. -/
noncomputable def toReal : IEEEFloat eb mb → Option ℝ
  | .nan          => none
  | .inf _        => none
  | .finite s e m => some (finiteValue s e m)

/-- Real or sentinel `0`.  Use only when the caller has already
    discharged the NaN/Inf cases — prefer `toReal` otherwise. -/
noncomputable def toRealOrZero : IEEEFloat eb mb → ℝ
  | .nan          => 0
  | .inf _        => 0
  | .finite s e m => finiteValue s e m

@[simp] theorem toReal_nan :
    toReal (.nan : IEEEFloat eb mb) = none := rfl

@[simp] theorem toReal_inf (s : Bool) :
    toReal (.inf s : IEEEFloat eb mb) = none := rfl

@[simp] theorem toReal_finite (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    toReal (.finite s e m) = some (finiteValue s e m) := rfl

/-- A real number is representable in `(eb, mb)` if some `finite`
    encoding's `finiteValue` equals it exactly.  Note: `Representable`
    is *exact* — rounding-aware membership is in `IEEEFloat.Round`. -/
def Representable (eb mb : Nat) (r : ℝ) : Prop :=
  ∃ (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)),
    finiteValue (eb := eb) (mb := mb) s e m = r

end IEEEFloat
