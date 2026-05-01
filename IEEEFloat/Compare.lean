import IEEEFloat.Ops

/-! # IEEE 754 §5.6 comparison and §5.3.1 min/max

Comparisons follow strict IEEE 754 §5.6 semantics:

  *  **NaN is unordered with everything (including itself).**  Every
     ordered comparison (`lt`, `le`) returns `false` whenever either
     operand is a NaN.  Equality (`eq`) likewise returns `false`.
     The `unordered` predicate captures this case explicitly.
  *  **`+0 = −0`.**  Despite their distinct bit patterns, the two
     signed zeros compare equal under `eq`/`le` and are *not* less
     than each other under `lt`.

`min` / `max` follow IEEE 754-2019 §5.3.1.  Two flavours:

  *  `minimum` / `maximum`: NaN-propagating.  Either operand a NaN
     forces a NaN result.  Sign-aware on ±0: `minimum +0 −0 = −0`,
     `maximum +0 −0 = +0`.
  *  `minimumNumber` / `maximumNumber`: NaN-skipping.  A NaN
     operand is dropped in favour of the other; only both-NaN
     produces NaN.  Same sign-aware ±0 handling.

All operations here are constructor-level and computable — no
`Real` arithmetic, no rounding.
-/

namespace IEEEFloat

variable {eb mb : Nat}

/-! ## Encoding-level magnitude

`(e.val * 2^mb + m.val)` linearises a finite encoding's magnitude
into a single `Nat`.  Subnormals (`e = 0`) use `(0, m)`, normals
use `(e, m)`; lex-comparing `(e, m)` agrees with magnitude order
for both regimes (and the boundary at the smallest normal). -/

/-- Encoding-level magnitude of a finite encoding, as a `Nat`. -/
def magNat : IEEEFloat eb mb → Nat
  | .finite _ e m => e.val * 2 ^ mb + m.val
  | _             => 0

@[simp] theorem magNat_finite (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    magNat (.finite s e m : IEEEFloat eb mb) = e.val * 2 ^ mb + m.val := rfl

/-! ## Comparison predicates -/

/-- IEEE 754 less-than.  Returns `false` if either operand is NaN
    (unordered case); treats `+0` and `−0` as equal. -/
def lt : IEEEFloat eb mb → IEEEFloat eb mb → Bool
  | .nan, _              => false
  | _, .nan              => false
  | .inf true,  .inf false  => true
  | .inf _,     .inf _      => false
  | .inf true,  .finite _ _ _ => true
  | .inf false, .finite _ _ _ => false
  | .finite _ _ _, .inf false => true
  | .finite _ _ _, .inf true  => false
  | .finite sx ex mx, .finite sy ey my =>
      let xMag := ex.val * 2 ^ mb + mx.val
      let yMag := ey.val * 2 ^ mb + my.val
      if xMag = 0 ∧ yMag = 0 then
        false  -- both zeros, equal regardless of sign
      else
        match sx, sy with
        | false, false => xMag < yMag       -- both positive
        | true,  true  => yMag < xMag       -- both negative (reversed)
        | false, true  => false             -- x ≥ 0, y < 0
        | true,  false => true              -- x < 0, y ≥ 0

/-- IEEE 754 equality.  Returns `false` if either operand is NaN;
    `+0 = −0` is `true`. -/
def eq : IEEEFloat eb mb → IEEEFloat eb mb → Bool
  | .nan, _ => false
  | _, .nan => false
  | .inf sx, .inf sy => sx = sy
  | .inf _, .finite _ _ _ => false
  | .finite _ _ _, .inf _ => false
  | .finite sx ex mx, .finite sy ey my =>
      let xMag := ex.val * 2 ^ mb + mx.val
      let yMag := ey.val * 2 ^ mb + my.val
      if xMag = 0 ∧ yMag = 0 then
        true  -- both zeros, equal regardless of sign
      else
        sx = sy ∧ xMag = yMag

/-- IEEE 754 less-than-or-equal.  `lt x y || eq x y`. -/
def le (x y : IEEEFloat eb mb) : Bool := lt x y || eq x y

/-- IEEE 754 unordered: at least one operand is NaN. -/
def unordered : IEEEFloat eb mb → IEEEFloat eb mb → Bool
  | .nan, _ => true
  | _, .nan => true
  | _, _    => false

/-! ### Comparison sanity theorems -/

@[simp] theorem lt_nan_left (y : IEEEFloat eb mb) :
    lt (.nan : IEEEFloat eb mb) y = false := rfl

@[simp] theorem lt_nan_right (x : IEEEFloat eb mb) :
    lt x (.nan : IEEEFloat eb mb) = false := by
  cases x <;> rfl

@[simp] theorem eq_nan_left (y : IEEEFloat eb mb) :
    eq (.nan : IEEEFloat eb mb) y = false := rfl

@[simp] theorem eq_nan_right (x : IEEEFloat eb mb) :
    eq x (.nan : IEEEFloat eb mb) = false := by
  cases x <;> rfl

@[simp] theorem unordered_nan_left (y : IEEEFloat eb mb) :
    unordered (.nan : IEEEFloat eb mb) y = true := rfl

@[simp] theorem unordered_nan_right (x : IEEEFloat eb mb) :
    unordered x (.nan : IEEEFloat eb mb) = true := by
  cases x <;> rfl

/-- `lt` is irreflexive: `lt x x = false` for every `x`. -/
theorem lt_irrefl (x : IEEEFloat eb mb) : lt x x = false := by
  cases x with
  | nan => rfl
  | inf s => cases s <;> rfl
  | finite s e m =>
    simp only [lt]
    split_ifs with h
    · rfl
    · rcases s <;> simp

/-- Equality on non-NaN encodings is reflexive. -/
theorem eq_self (x : IEEEFloat eb mb) (hx : x ≠ .nan) : eq x x = true := by
  cases x with
  | nan => exact absurd rfl hx
  | inf s => simp [eq]
  | finite s e m =>
    simp only [eq]
    split_ifs with h
    · rfl
    · simp

/-- `+0 = −0`: the two signed zeros compare equal. -/
theorem eq_pos_neg_zero
    (h_e_pos : 0 < 2 ^ eb - 1) (h_m_pos : 0 < 2 ^ mb) :
    eq (.finite false ⟨0, h_e_pos⟩ ⟨0, h_m_pos⟩ : IEEEFloat eb mb)
       (.finite true  ⟨0, h_e_pos⟩ ⟨0, h_m_pos⟩) = true := by
  simp [eq]

/-- `+0 < −0` is false (and `−0 < +0` likewise). -/
theorem lt_pos_neg_zero
    (h_e_pos : 0 < 2 ^ eb - 1) (h_m_pos : 0 < 2 ^ mb) :
    lt (.finite false ⟨0, h_e_pos⟩ ⟨0, h_m_pos⟩ : IEEEFloat eb mb)
       (.finite true  ⟨0, h_e_pos⟩ ⟨0, h_m_pos⟩) = false := by
  simp [lt]

/-! ## min / max

Implementation strategy: dispatch NaN cases via constructor match,
then handle the non-NaN branch via `lt`.  When `lt x y = false` and
`lt y x = false`, the values compare equal — but `+0` and `−0` need
disambiguating, and that's where the sign-bit tiebreak comes in. -/

/-- IEEE 754 minimum: NaN-propagating.  On `±0` operands, returns
    `−0` (preferring the negative sign). -/
def minimum : IEEEFloat eb mb → IEEEFloat eb mb → IEEEFloat eb mb
  | .nan, _ => .nan
  | _, .nan => .nan
  | x, y =>
      if lt x y then x
      else if lt y x then y
      else if x.signBit then x else y

/-- IEEE 754 maximum: NaN-propagating.  On `±0` operands, returns
    `+0` (preferring the positive sign). -/
def maximum : IEEEFloat eb mb → IEEEFloat eb mb → IEEEFloat eb mb
  | .nan, _ => .nan
  | _, .nan => .nan
  | x, y =>
      if lt y x then x
      else if lt x y then y
      else if x.signBit then y else x

/-- IEEE 754 minimumNumber: NaN-skipping.  Returns the non-NaN
    operand if exactly one is NaN; both-NaN gives NaN. -/
def minimumNumber : IEEEFloat eb mb → IEEEFloat eb mb → IEEEFloat eb mb
  | .nan, .nan => .nan
  | .nan, y    => y
  | x, .nan    => x
  | x, y       =>
      if lt x y then x
      else if lt y x then y
      else if x.signBit then x else y

/-- IEEE 754 maximumNumber: NaN-skipping.  Returns the non-NaN
    operand if exactly one is NaN; both-NaN gives NaN. -/
def maximumNumber : IEEEFloat eb mb → IEEEFloat eb mb → IEEEFloat eb mb
  | .nan, .nan => .nan
  | .nan, y    => y
  | x, .nan    => x
  | x, y       =>
      if lt y x then x
      else if lt x y then y
      else if x.signBit then y else x

/-! ### min/max sanity theorems -/

@[simp] theorem minimum_nan_left (y : IEEEFloat eb mb) :
    minimum (.nan : IEEEFloat eb mb) y = .nan := rfl
@[simp] theorem minimum_nan_right (x : IEEEFloat eb mb) :
    minimum x (.nan : IEEEFloat eb mb) = .nan := by cases x <;> rfl

@[simp] theorem maximum_nan_left (y : IEEEFloat eb mb) :
    maximum (.nan : IEEEFloat eb mb) y = .nan := rfl
@[simp] theorem maximum_nan_right (x : IEEEFloat eb mb) :
    maximum x (.nan : IEEEFloat eb mb) = .nan := by cases x <;> rfl

@[simp] theorem minimumNumber_nan_nan :
    minimumNumber (.nan : IEEEFloat eb mb) .nan = .nan := rfl
@[simp] theorem minimumNumber_nan_left (y : IEEEFloat eb mb) (hy : y ≠ .nan) :
    minimumNumber (.nan : IEEEFloat eb mb) y = y := by
  cases y with
  | nan => exact absurd rfl hy
  | inf _ => rfl
  | finite _ _ _ => rfl
@[simp] theorem minimumNumber_nan_right (x : IEEEFloat eb mb) (hx : x ≠ .nan) :
    minimumNumber x (.nan : IEEEFloat eb mb) = x := by
  cases x with
  | nan => exact absurd rfl hx
  | inf _ => rfl
  | finite _ _ _ => rfl

@[simp] theorem maximumNumber_nan_nan :
    maximumNumber (.nan : IEEEFloat eb mb) .nan = .nan := rfl
@[simp] theorem maximumNumber_nan_left (y : IEEEFloat eb mb) (hy : y ≠ .nan) :
    maximumNumber (.nan : IEEEFloat eb mb) y = y := by
  cases y with
  | nan => exact absurd rfl hy
  | inf _ => rfl
  | finite _ _ _ => rfl
@[simp] theorem maximumNumber_nan_right (x : IEEEFloat eb mb) (hx : x ≠ .nan) :
    maximumNumber x (.nan : IEEEFloat eb mb) = x := by
  cases x with
  | nan => exact absurd rfl hx
  | inf _ => rfl
  | finite _ _ _ => rfl

/-- `minimum +0 −0 = −0` (sign-aware on signed zeros). -/
theorem minimum_pos_neg_zero
    (h_e_pos : 0 < 2 ^ eb - 1) (h_m_pos : 0 < 2 ^ mb) :
    minimum (.finite false ⟨0, h_e_pos⟩ ⟨0, h_m_pos⟩ : IEEEFloat eb mb)
            (.finite true  ⟨0, h_e_pos⟩ ⟨0, h_m_pos⟩)
      = .finite true ⟨0, h_e_pos⟩ ⟨0, h_m_pos⟩ := by
  simp [minimum, lt, signBit]

/-- `maximum +0 −0 = +0` (sign-aware on signed zeros). -/
theorem maximum_pos_neg_zero
    (h_e_pos : 0 < 2 ^ eb - 1) (h_m_pos : 0 < 2 ^ mb) :
    maximum (.finite false ⟨0, h_e_pos⟩ ⟨0, h_m_pos⟩ : IEEEFloat eb mb)
            (.finite true  ⟨0, h_e_pos⟩ ⟨0, h_m_pos⟩)
      = .finite false ⟨0, h_e_pos⟩ ⟨0, h_m_pos⟩ := by
  simp [maximum, lt, signBit]

end IEEEFloat
