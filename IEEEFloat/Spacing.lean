import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import IEEEFloat.Real

/-! # Spacing of representable values

This module sets up the bit-level neighborhood structure of finite
IEEE encodings: `ulp` (gap to the encoding-adjacent neighbour) and
`nextFinite` / `prevFinite` (encoding successors/predecessors).

These are the building blocks for the **half-ULP distance bound**
(any RN result is within ½ ulp of its input) and the **RNE
tie-break existence theorem** (any midpoint tie set contains an
even-mantissa element).  Both depend on real-value monotonicity of
the encoding successor — that monotonicity proof is its own
substantial piece (roughly: bit-level case analysis on
positive/negative × normal/subnormal × exponent-boundary × ±0
crossing) and lives in a follow-up commit.

This commit ships **definitions and a handful of simp-rewrites**
only; theorems about monotonicity, adjacency, and parity-alternation
are deliberately deferred so the constructive scaffolding lands
under review without sorry'd or axiomatized claims.

## Notes on encoding-vs-value adjacency

`nextFinite` is defined at the *encoding* level: it returns the next
distinct encoding in real-value-non-decreasing order.  `−0 → +0` is
therefore a step (different encoding, same real value); a separate
`nextValue` notion that quotients by real-value-equality is the
right primitive for proofs that need to skip the ±0 plateau.  We
defer it until a consumer needs it.
-/

namespace IEEEFloat

variable {eb mb : Nat}

/-! ## Unit in the last place (ulp)

`ulp x` is the distance to `x`'s encoding-adjacent neighbour
*above* (toward larger real values).  For nonfinite `x` we return
`0` as a sentinel — callers should guard on `isFinite`.

  *  Normal `(e ≠ 0)`:    `ulp = 2^(e − bias − mb)`.
  *  Subnormal `(e = 0)`: `ulp = 2^(1 − bias − mb) = 2^minSubnormalExp`.
  *  Nan / ±∞:            `ulp = 0` (sentinel; callers should avoid).

Note that `ulp` is the gap *upward* (encoding-wise); the gap
*downward* equals `ulp x` within an exponent stratum but equals
`ulp x / 2` when `x` is at a power-of-two boundary (mantissa zero,
normal exponent ≥ 2).  Half-ULP-bound proofs that care about the
asymmetric stratum boundary need both. -/

noncomputable def ulp : IEEEFloat eb mb → ℝ
  | .finite _ e _ =>
      if e.val = 0 then
        (2 : ℝ) ^ minSubnormalExp eb mb
      else
        (2 : ℝ) ^ ((e.val : Int) - bias eb - mb)
  | _ => 0

@[simp] theorem ulp_nan : ulp (.nan : IEEEFloat eb mb) = 0 := rfl
@[simp] theorem ulp_inf (s : Bool) : ulp (.inf s : IEEEFloat eb mb) = 0 := rfl

/-! ## Encoding successor / predecessor

`nextFinite x` is the unique encoding-adjacent value strictly
greater than `x` in real value (or `+∞` for the largest finite, or
the same encoding `+∞` / `NaN` for nonfinite inputs).  Sign-magnitude
encoding makes the four cases nontrivial:

  *  positive non-max-mantissa: bump mantissa.
  *  positive max-mantissa, non-max-exp: zero mantissa, bump exponent.
  *  positive max-mantissa, max-exp: → `+∞` (overflow).
  *  negative non-zero-mantissa: decrement mantissa (toward zero).
  *  negative zero-mantissa, non-zero-exp: max mantissa, decrement exp.
  *  negative zero-mantissa, zero-exp (i.e., `−0`): → `+0`.
  *  `−∞`: → most-negative-finite.
  *  `+∞` / NaN: identity (no successor).

`prevFinite` is the mirror.  We define both and leave their
real-value-monotonicity proofs to a follow-up.
-/

/-- Successor in encoding order.  See module doc for case structure. -/
def nextFinite : IEEEFloat eb mb → IEEEFloat eb mb
  -- positive finites: increase
  | .finite false e m =>
      if h_m : m.val + 1 < 2 ^ mb then
        .finite false e ⟨m.val + 1, h_m⟩
      else
        -- mantissa overflows; bump exponent
        if h_e : e.val + 1 < 2 ^ eb - 1 then
          .finite false ⟨e.val + 1, h_e⟩ ⟨0, Nat.pow_pos (by decide : 0 < 2)⟩
        else
          -- exponent overflows; → +∞
          .inf false
  -- negative finites: increase means decrease in magnitude
  | .finite true e m =>
      if h_m : m.val ≠ 0 then
        .finite true e ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) m.isLt⟩
      else
        -- mantissa is 0; either bump down exponent or cross zero
        if h_e : e.val ≠ 0 then
          have h_pred : e.val - 1 < 2 ^ eb - 1 :=
            lt_of_le_of_lt (Nat.sub_le _ _) e.isLt
          have h_max : 2 ^ mb - 1 < 2 ^ mb := by
            have h2 : 0 < 2 ^ mb := Nat.pow_pos (by decide : 0 < 2)
            omega
          .finite true ⟨e.val - 1, h_pred⟩ ⟨2 ^ mb - 1, h_max⟩
        else
          -- e = 0, m = 0: this is −0; successor in real-value is +0
          -- (same value, different encoding; the "strict next value"
          -- is +smallest-subnormal, but we step encoding-wise here)
          .finite false e m
  -- −∞: successor is most-negative-finite (mantissa max, exp max)
  | .inf true =>
      if h_e : 2 ^ eb - 2 < 2 ^ eb - 1 then
        if h_m : 2 ^ mb - 1 < 2 ^ mb then
          .finite true ⟨2 ^ eb - 2, h_e⟩ ⟨2 ^ mb - 1, h_m⟩
        else .inf true  -- degenerate (2^mb = 0; impossible since 2^mb ≥ 1)
      else .inf true    -- degenerate (eb < 1)
  -- +∞ and NaN: identity (no successor)
  | .inf false => .inf false
  | .nan       => .nan

/-- Predecessor in encoding order.  Mirror of `nextFinite`. -/
def prevFinite : IEEEFloat eb mb → IEEEFloat eb mb
  -- negative finites: decrease means increase in magnitude
  | .finite true e m =>
      if h_m : m.val + 1 < 2 ^ mb then
        .finite true e ⟨m.val + 1, h_m⟩
      else
        if h_e : e.val + 1 < 2 ^ eb - 1 then
          .finite true ⟨e.val + 1, h_e⟩ ⟨0, Nat.pow_pos (by decide : 0 < 2)⟩
        else
          .inf true
  -- positive finites: decrease toward zero
  | .finite false e m =>
      if h_m : m.val ≠ 0 then
        .finite false e ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) m.isLt⟩
      else
        if h_e : e.val ≠ 0 then
          have h_pred : e.val - 1 < 2 ^ eb - 1 :=
            lt_of_le_of_lt (Nat.sub_le _ _) e.isLt
          have h_max : 2 ^ mb - 1 < 2 ^ mb := by
            have h2 : 0 < 2 ^ mb := Nat.pow_pos (by decide : 0 < 2)
            omega
          .finite false ⟨e.val - 1, h_pred⟩ ⟨2 ^ mb - 1, h_max⟩
        else
          -- e = 0, m = 0: this is +0; predecessor in real-value is −0
          .finite true e m
  | .inf false =>
      if h_e : 2 ^ eb - 2 < 2 ^ eb - 1 then
        if h_m : 2 ^ mb - 1 < 2 ^ mb then
          .finite false ⟨2 ^ eb - 2, h_e⟩ ⟨2 ^ mb - 1, h_m⟩
        else .inf false
      else .inf false
  | .inf true => .inf true
  | .nan      => .nan

/-! ## Basic positivity

The ulp of a finite encoding is a real power of two — strictly
positive.  This is the cheapest property of `ulp` and it discharges
in both branches of the `if e.val = 0` split via `zpow_pos`. -/

theorem ulp_pos_of_finite {x : IEEEFloat eb mb} (hx : x.isFinite = true) :
    0 < ulp x := by
  match x, hx with
  | .finite _ e _, _ =>
    simp only [ulp]
    split
    · exact zpow_pos (by norm_num : (0 : ℝ) < 2) _
    · exact zpow_pos (by norm_num : (0 : ℝ) < 2) _

/-! ## Real-value gap lemmas

The four cases of `nextFinite` for finite-to-finite transitions:

  *  positive within-stratum (m+1 < 2^mb): gap = ulp.
  *  positive cross-stratum (m = 2^mb-1, e+1 < 2^eb-1): gap = ulp.
  *  negative within-stratum (m > 0): gap = ulp.
  *  negative cross-stratum (m = 0, e > 0): gap = ulp / 2 (lower stratum).
  *  −0 → +0: gap = 0.

These are proved case by case below.  The shared `Real`-arithmetic
core is the algebraic identity `2^a · (1 + (m+1)/2^mb) − 2^a · (1 + m/2^mb) = 2^(a − mb)`
and similar.
-/

/-- Helper: `2^mb : ℝ` is positive and nonzero. -/
theorem two_pow_mb_pos : (0 : ℝ) < (2 : ℝ) ^ mb :=
  pow_pos (by norm_num : (0 : ℝ) < 2) mb

theorem two_pow_mb_ne : ((2 : ℝ) ^ mb) ≠ 0 := ne_of_gt two_pow_mb_pos

/-- Algebraic helper: `2^(a − mb) = 2^a · (2^mb)⁻¹` when `mb : Nat` and `a : Int`. -/
theorem zpow_sub_natCast (a : Int) (n : Nat) :
    (2 : ℝ) ^ (a - (n : Int)) = (2 : ℝ) ^ a * ((2 : ℝ) ^ n)⁻¹ := by
  rw [show (a - (n : Int)) = a + (-(n : Int)) from by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      zpow_neg, zpow_natCast]

/-- Positive within-stratum: `(false, e, m) → (false, e, m+1)`. -/
theorem nextFinite_value_pos_within
    (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) (h : m.val + 1 < 2 ^ mb) :
    finiteValue (eb := eb) (mb := mb) false e ⟨m.val + 1, h⟩
      = finiteValue (eb := eb) (mb := mb) false e m
        + ulp (.finite false e m : IEEEFloat eb mb) := by
  have h2ne : ((2 : ℝ) ^ mb) ≠ 0 := two_pow_mb_ne
  simp only [finiteValue, ulp, if_false_left, if_pos]
  by_cases he : e.val = 0
  · simp only [he, ↓reduceIte]
    -- subnormal: 2^minNormalExp * (m+1)/2^mb = 2^minNormalExp * m/2^mb + 2^minSubnormalExp
    -- 2^minSubnormalExp = 2^(minNormalExp - mb) = 2^minNormalExp / 2^mb
    rw [show minSubnormalExp eb mb = minNormalExp eb - (mb : Int) from rfl,
        zpow_sub_natCast]
    push_cast
    field_simp
  · simp only [he, ↓reduceIte]
    -- normal: 2^(e - bias) * (1 + (m+1)/2^mb) = 2^(e - bias) * (1 + m/2^mb) + 2^(e - bias - mb)
    rw [zpow_sub_natCast]
    push_cast
    field_simp
    ring

/-- Negative within-stratum: `(true, e, m+1) → (true, e, m)` (decrement).
    Stated as: the *predecessor* of `(true, e, m)` (less negative) has value
    differing by ulp.  This is `(true, e, m).value − (true, e, m-1).value = ulp`,
    rephrased so we don't need a `m > 0` precondition on the input. -/
theorem finiteValue_neg_within_diff
    (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) (h : m.val + 1 < 2 ^ mb) :
    finiteValue (eb := eb) (mb := mb) true e m
      = finiteValue (eb := eb) (mb := mb) true e ⟨m.val + 1, h⟩
        + ulp (.finite true e m : IEEEFloat eb mb) := by
  have h2ne : ((2 : ℝ) ^ mb) ≠ 0 := two_pow_mb_ne
  simp only [finiteValue, ulp]
  by_cases he : e.val = 0
  · simp only [he, ↓reduceIte]
    rw [show minSubnormalExp eb mb = minNormalExp eb - (mb : Int) from rfl,
        zpow_sub_natCast]
    push_cast
    field_simp
    ring
  · simp only [he, ↓reduceIte]
    rw [zpow_sub_natCast]
    push_cast
    field_simp
    ring

/-! ## Cross-stratum gap lemmas

These cover the encoding transition where the mantissa wraps from
its maximum / minimum and the exponent shifts.  Stated as
"value-difference = explicit power of two" instead of routed
through `ulp`, because at the negative cross-stratum the gap is
*half* the larger stratum's ulp — which makes a `ulp`-routed
statement awkward. -/

/-- `Nat`-cast of `2^mb - 1` to `ℝ` equals `2^mb - 1` in `ℝ`. -/
theorem cast_two_pow_sub_one :
    ((2 ^ mb - 1 : Nat) : ℝ) = (2 : ℝ) ^ mb - 1 := by
  have h : 1 ≤ 2 ^ mb := Nat.one_le_iff_ne_zero.mpr (Nat.pow_pos (by decide : 0 < 2)).ne'
  rw [Nat.cast_sub h, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]

/-- Positive cross-stratum, old subnormal: `(false, 0, 2^mb-1) → (false, 1, 0)`.
    Gap = `2^minSubnormalExp` = subnormal-stratum ulp. -/
theorem finiteValue_pos_cross_subnormal_diff
    {eb mb : Nat} (h_e_new : (1 : Nat) < 2 ^ eb - 1) (h_e_old : (0 : Nat) < 2 ^ eb - 1)
    (h_max : 2 ^ mb - 1 < 2 ^ mb) (h_zero : 0 < 2 ^ mb) :
    finiteValue (eb := eb) (mb := mb) false ⟨1, h_e_new⟩ ⟨0, h_zero⟩
      - finiteValue (eb := eb) (mb := mb) false ⟨0, h_e_old⟩ ⟨2 ^ mb - 1, h_max⟩
      = (2 : ℝ) ^ minSubnormalExp eb mb := by
  have h2ne : ((2 : ℝ) ^ mb) ≠ 0 := two_pow_mb_ne
  have h_e_old_eq : (⟨0, h_e_old⟩ : Fin (2 ^ eb - 1)).val = 0 := rfl
  have h_e_new_ne : (⟨1, h_e_new⟩ : Fin (2 ^ eb - 1)).val ≠ 0 := by
    show (1 : Nat) ≠ 0; decide
  simp only [finiteValue, h_e_old_eq, h_e_new_ne, ↓reduceIte, if_true]
  rw [show minSubnormalExp eb mb = minNormalExp eb - (mb : Int) from rfl,
      zpow_sub_natCast]
  rw [show (((1 : Nat) : Int) - bias eb) = minNormalExp eb from by
      simp [minNormalExp]]
  push_cast
  rw [cast_two_pow_sub_one]
  field_simp
  ring

/-- Positive cross-stratum, old normal: `(false, e, 2^mb-1) → (false, e+1, 0)`
    where `e ≥ 1`.  Gap = `2^(e − bias − mb)`, the e-stratum ulp. -/
theorem finiteValue_pos_cross_normal_diff
    (e_old : Nat) (h_e_pos : 1 ≤ e_old)
    (h_e_old_lt : e_old < 2 ^ eb - 1)
    (h_e_new : e_old + 1 < 2 ^ eb - 1)
    (h_max : 2 ^ mb - 1 < 2 ^ mb) (h_zero : 0 < 2 ^ mb) :
    finiteValue (eb := eb) (mb := mb) false ⟨e_old + 1, h_e_new⟩ ⟨0, h_zero⟩
      - finiteValue (eb := eb) (mb := mb) false ⟨e_old, h_e_old_lt⟩ ⟨2 ^ mb - 1, h_max⟩
      = (2 : ℝ) ^ ((e_old : Int) - bias eb - (mb : Int)) := by
  have h2ne : ((2 : ℝ) ^ mb) ≠ 0 := two_pow_mb_ne
  have h_e_old_ne : (⟨e_old, h_e_old_lt⟩ : Fin (2 ^ eb - 1)).val ≠ 0 := by
    show e_old ≠ 0; exact Nat.one_le_iff_ne_zero.mp h_e_pos
  have h_e_new_ne : (⟨e_old + 1, h_e_new⟩ : Fin (2 ^ eb - 1)).val ≠ 0 := by
    show e_old + 1 ≠ 0; exact Nat.succ_ne_zero _
  simp only [finiteValue, h_e_old_ne, h_e_new_ne, ↓reduceIte]
  -- Cast e_old + 1 to Int
  rw [show ((e_old + 1 : Nat) : Int) = (e_old : Int) + 1 from by push_cast; ring]
  -- 2^((e_old : Int) + 1 - bias) = 2^((e_old : Int) - bias) * 2
  rw [show (e_old : Int) + 1 - bias eb = ((e_old : Int) - bias eb) + 1 from by ring,
      zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [zpow_sub_natCast]
  push_cast
  rw [cast_two_pow_sub_one]
  field_simp
  ring

/-- Negative cross-stratum, new subnormal: `(true, 1, 0) → (true, 0, 2^mb-1)`.
    Gap = `2^minSubnormalExp`. -/
theorem finiteValue_neg_cross_to_subnormal_diff
    {eb mb : Nat} (h_e_old : (1 : Nat) < 2 ^ eb - 1) (h_e_new : (0 : Nat) < 2 ^ eb - 1)
    (h_max : 2 ^ mb - 1 < 2 ^ mb) (h_zero : 0 < 2 ^ mb) :
    finiteValue (eb := eb) (mb := mb) true ⟨0, h_e_new⟩ ⟨2 ^ mb - 1, h_max⟩
      - finiteValue (eb := eb) (mb := mb) true ⟨1, h_e_old⟩ ⟨0, h_zero⟩
      = (2 : ℝ) ^ minSubnormalExp eb mb := by
  have h2ne : ((2 : ℝ) ^ mb) ≠ 0 := two_pow_mb_ne
  have h_e_old_ne : (⟨1, h_e_old⟩ : Fin (2 ^ eb - 1)).val ≠ 0 := by
    show (1 : Nat) ≠ 0; decide
  have h_e_new_eq : (⟨0, h_e_new⟩ : Fin (2 ^ eb - 1)).val = 0 := rfl
  simp only [finiteValue, h_e_old_ne, h_e_new_eq, ↓reduceIte]
  rw [show minSubnormalExp eb mb = minNormalExp eb - (mb : Int) from rfl,
      zpow_sub_natCast]
  rw [show (((1 : Nat) : Int) - bias eb) = minNormalExp eb from by
      simp [minNormalExp]]
  push_cast
  rw [cast_two_pow_sub_one]
  field_simp
  ring

/-- Negative cross-stratum, new normal: `(true, e, 0) → (true, e-1, 2^mb-1)`
    where `e ≥ 2`.  Gap = `2^(e − 1 − bias − mb)`, half the e-stratum ulp. -/
theorem finiteValue_neg_cross_to_normal_diff
    (e_old : Nat) (h_e_pos : 2 ≤ e_old)
    (h_e_old_lt : e_old < 2 ^ eb - 1)
    (h_e_new : e_old - 1 < 2 ^ eb - 1)
    (h_max : 2 ^ mb - 1 < 2 ^ mb) (h_zero : 0 < 2 ^ mb) :
    finiteValue (eb := eb) (mb := mb) true ⟨e_old - 1, h_e_new⟩ ⟨2 ^ mb - 1, h_max⟩
      - finiteValue (eb := eb) (mb := mb) true ⟨e_old, h_e_old_lt⟩ ⟨0, h_zero⟩
      = (2 : ℝ) ^ ((e_old : Int) - 1 - bias eb - (mb : Int)) := by
  have h2ne : ((2 : ℝ) ^ mb) ≠ 0 := two_pow_mb_ne
  have h_e_old_ne : (⟨e_old, h_e_old_lt⟩ : Fin (2 ^ eb - 1)).val ≠ 0 := by
    show e_old ≠ 0; omega
  have h_e_new_ne : (⟨e_old - 1, h_e_new⟩ : Fin (2 ^ eb - 1)).val ≠ 0 := by
    show e_old - 1 ≠ 0; omega
  have h_e_old_le : 1 ≤ e_old := by omega
  simp only [finiteValue, h_e_old_ne, h_e_new_ne, ↓reduceIte]
  -- Cast e_old - 1 to Int; reassociate to factor out 2^((e_old : Int) - bias eb)
  rw [show ((e_old - 1 : Nat) : Int) = (e_old : Int) - 1 from
        by rw [Nat.cast_sub h_e_old_le]; push_cast; ring,
      show (e_old : Int) - 1 - bias eb = ((e_old : Int) - bias eb) - 1 from by ring,
      zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [show ((e_old : Int) - bias eb) - 1 - (mb : Int)
        = ((e_old : Int) - bias eb - (mb : Int)) - 1 from by ring,
      zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_sub_natCast]
  push_cast
  rw [cast_two_pow_sub_one]
  field_simp
  ring

/-! ## Zero values -/

@[simp] theorem finiteValue_zero_neg
    (h_e : 0 < 2 ^ eb - 1) (h_m : 0 < 2 ^ mb) :
    finiteValue (eb := eb) (mb := mb) true ⟨0, h_e⟩ ⟨0, h_m⟩ = 0 := by
  simp [finiteValue]

@[simp] theorem finiteValue_zero_pos
    (h_e : 0 < 2 ^ eb - 1) (h_m : 0 < 2 ^ mb) :
    finiteValue (eb := eb) (mb := mb) false ⟨0, h_e⟩ ⟨0, h_m⟩ = 0 := by
  simp [finiteValue]

/-! ## `toRealOrZero` rewrites for the three constructor heads. -/

@[simp] theorem toRealOrZero_finite_eq (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    toRealOrZero (.finite s e m : IEEEFloat eb mb) = finiteValue s e m := rfl

@[simp] theorem toRealOrZero_nan : toRealOrZero (.nan : IEEEFloat eb mb) = 0 := rfl

@[simp] theorem toRealOrZero_inf (s : Bool) :
    toRealOrZero (.inf s : IEEEFloat eb mb) = 0 := rfl

/-! ## `finiteValue` injectivity modulo ±0

Two finite encodings `(s₁, e₁, m₁)` and `(s₂, e₂, m₂)` with the same
real value must be equal as encodings, with one exception: both
`±0` encodings (`(s, 0, 0)`) decode to `0`, so the sign bit is
unconstrained when the value is zero.

Proved by case analysis on whether each exponent is zero (sub-
normal) or non-zero (normal), with mixed cases impossible because
subnormal magnitudes are `< 2^minNormalExp` while normal magnitudes
are `≥ 2^minNormalExp`. -/

private theorem finiteValue_normal_pos
    {s : Bool} {e : Fin (2 ^ eb - 1)} {m : Fin (2 ^ mb)}
    (he : e.val ≠ 0) :
    0 < (2 : ℝ) ^ ((e.val : Int) - bias eb) * (1 + (m.val : ℝ) / (2 : ℝ) ^ mb) := by
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ ((e.val : Int) - bias eb) :=
    zpow_pos (by norm_num) _
  have h2mb_pos : (0 : ℝ) < (2 : ℝ) ^ mb := two_pow_mb_pos
  have hmnn : (0 : ℝ) ≤ (m.val : ℝ) / (2 : ℝ) ^ mb :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt h2mb_pos)
  have : (1 : ℝ) ≤ 1 + (m.val : ℝ) / (2 : ℝ) ^ mb := by linarith
  positivity

private theorem finiteValue_normal_lt_two_pow
    {s : Bool} (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) (he : e.val ≠ 0) :
    (2 : ℝ) ^ ((e.val : Int) - bias eb) * (1 + (m.val : ℝ) / (2 : ℝ) ^ mb)
      < (2 : ℝ) ^ ((e.val : Int) + 1 - bias eb) := by
  have h2mb_pos : (0 : ℝ) < (2 : ℝ) ^ mb := two_pow_mb_pos
  have hm_lt : (m.val : ℝ) / (2 : ℝ) ^ mb < 1 := by
    rw [div_lt_one h2mb_pos]
    have : (m.val : ℝ) < ((2 : Nat) ^ mb : Nat) := by exact_mod_cast m.isLt
    convert this using 1
    push_cast
    rfl
  have h_factor_lt : 1 + (m.val : ℝ) / (2 : ℝ) ^ mb < 2 := by linarith
  have h2 : (2 : ℝ) ^ ((e.val : Int) + 1 - bias eb)
          = (2 : ℝ) ^ ((e.val : Int) - bias eb) * 2 := by
    rw [show ((e.val : Int) + 1 - bias eb) = ((e.val : Int) - bias eb) + 1 from by ring,
        zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [h2]
  have h2zpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((e.val : Int) - bias eb) :=
    zpow_pos (by norm_num) _
  exact mul_lt_mul_of_pos_left h_factor_lt h2zpow_pos

/-! ## Strict gap inequalities (real-value monotonicity per case)

Each of these is the gap lemma rephrased as a strict inequality
plus the fact that `2^k > 0`. -/

theorem finiteValue_pos_within_lt
    (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) (h : m.val + 1 < 2 ^ mb) :
    finiteValue (eb := eb) (mb := mb) false e m
      < finiteValue (eb := eb) (mb := mb) false e ⟨m.val + 1, h⟩ := by
  rw [nextFinite_value_pos_within e m h]
  have := ulp_pos_of_finite (x := (.finite false e m : IEEEFloat eb mb)) rfl
  linarith

theorem finiteValue_neg_within_lt
    (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) (h : m.val + 1 < 2 ^ mb) :
    finiteValue (eb := eb) (mb := mb) true e ⟨m.val + 1, h⟩
      < finiteValue (eb := eb) (mb := mb) true e m := by
  rw [finiteValue_neg_within_diff e m h]
  have := ulp_pos_of_finite (x := (.finite true e m : IEEEFloat eb mb)) rfl
  linarith

theorem finiteValue_pos_cross_subnormal_lt
    {eb mb : Nat} (h_e_old : (0 : Nat) < 2 ^ eb - 1) (h_e_new : (1 : Nat) < 2 ^ eb - 1)
    (h_max : 2 ^ mb - 1 < 2 ^ mb) (h_zero : 0 < 2 ^ mb) :
    finiteValue (eb := eb) (mb := mb) false ⟨0, h_e_old⟩ ⟨2 ^ mb - 1, h_max⟩
      < finiteValue (eb := eb) (mb := mb) false ⟨1, h_e_new⟩ ⟨0, h_zero⟩ := by
  have hgap := finiteValue_pos_cross_subnormal_diff (eb := eb) (mb := mb)
    h_e_new h_e_old h_max h_zero
  have hpos : (0 : ℝ) < (2 : ℝ) ^ minSubnormalExp eb mb := zpow_pos (by norm_num) _
  linarith

theorem finiteValue_pos_cross_normal_lt
    (e_old : Nat) (h_e_pos : 1 ≤ e_old)
    (h_e_old_lt : e_old < 2 ^ eb - 1)
    (h_e_new : e_old + 1 < 2 ^ eb - 1)
    (h_max : 2 ^ mb - 1 < 2 ^ mb) (h_zero : 0 < 2 ^ mb) :
    finiteValue (eb := eb) (mb := mb) false ⟨e_old, h_e_old_lt⟩ ⟨2 ^ mb - 1, h_max⟩
      < finiteValue (eb := eb) (mb := mb) false ⟨e_old + 1, h_e_new⟩ ⟨0, h_zero⟩ := by
  have hgap := finiteValue_pos_cross_normal_diff (eb := eb) (mb := mb)
    e_old h_e_pos h_e_old_lt h_e_new h_max h_zero
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((e_old : Int) - bias eb - (mb : Int)) :=
    zpow_pos (by norm_num) _
  linarith

theorem finiteValue_neg_cross_to_subnormal_lt
    {eb mb : Nat} (h_e_old : (1 : Nat) < 2 ^ eb - 1) (h_e_new : (0 : Nat) < 2 ^ eb - 1)
    (h_max : 2 ^ mb - 1 < 2 ^ mb) (h_zero : 0 < 2 ^ mb) :
    finiteValue (eb := eb) (mb := mb) true ⟨1, h_e_old⟩ ⟨0, h_zero⟩
      < finiteValue (eb := eb) (mb := mb) true ⟨0, h_e_new⟩ ⟨2 ^ mb - 1, h_max⟩ := by
  have hgap := finiteValue_neg_cross_to_subnormal_diff (eb := eb) (mb := mb)
    h_e_old h_e_new h_max h_zero
  have hpos : (0 : ℝ) < (2 : ℝ) ^ minSubnormalExp eb mb := zpow_pos (by norm_num) _
  linarith

theorem finiteValue_neg_cross_to_normal_lt
    (e_old : Nat) (h_e_pos : 2 ≤ e_old)
    (h_e_old_lt : e_old < 2 ^ eb - 1)
    (h_e_new : e_old - 1 < 2 ^ eb - 1)
    (h_max : 2 ^ mb - 1 < 2 ^ mb) (h_zero : 0 < 2 ^ mb) :
    finiteValue (eb := eb) (mb := mb) true ⟨e_old, h_e_old_lt⟩ ⟨0, h_zero⟩
      < finiteValue (eb := eb) (mb := mb) true ⟨e_old - 1, h_e_new⟩ ⟨2 ^ mb - 1, h_max⟩ := by
  have hgap := finiteValue_neg_cross_to_normal_diff (eb := eb) (mb := mb)
    e_old h_e_pos h_e_old_lt h_e_new h_max h_zero
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((e_old : Int) - 1 - bias eb - (mb : Int)) :=
    zpow_pos (by norm_num) _
  linarith

/-! ## Mantissa-LSB alternation

For `mb ≥ 1`, every encoding-adjacent pair (a finite `x` with
`nextFinite x` finite) has differing mantissa LSBs — except the
`−0 → +0` step, where both are zero (even).

Cases of `nextFinite` (finite-to-finite):
  *  positive within: `m → m+1`. Parity flips.
  *  positive cross:  `m = 2^mb−1 → m = 0`. (2^mb−1)%2 = 1 vs 0 — differ.
  *  negative within: `m → m−1`. Parity flips.
  *  negative cross:  `m = 0 → m = 2^mb−1`. 0 vs 1 — differ.
  *  `−0 → +0`: both `m = 0`, both parity 0. -/

private theorem two_pow_sub_one_mod_two (h : 1 ≤ mb) : (2 ^ mb - 1) % 2 = 1 := by
  have h_two : (2 : Nat) ∣ 2 ^ mb := dvd_pow_self 2 (Nat.one_le_iff_ne_zero.mp h)
  have h_two_le : 2 ≤ 2 ^ mb := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ mb := Nat.pow_le_pow_right (by norm_num) h
  omega

theorem nextFinite_mantissaLSB_diff_or_zero
    (x : IEEEFloat eb mb) (h_fin : x.isFinite = true)
    (h_succ_fin : (nextFinite x).isFinite = true) (h_mb : 1 ≤ mb) :
    x.mantissaLSB ≠ (nextFinite x).mantissaLSB ∨
    (x.mantissaLSB = 0 ∧ (nextFinite x).mantissaLSB = 0) := by
  match x, h_fin with
  | .finite false e m, _ =>
      simp only [nextFinite] at h_succ_fin ⊢
      split
      · rename_i h_m
        simp only [mantissaLSB_finite]
        left; omega
      · rename_i h_m
        split
        · rename_i h_e
          simp only [mantissaLSB_finite]
          have h_m_eq : m.val = 2 ^ mb - 1 := by have := m.isLt; omega
          left
          rw [h_m_eq, two_pow_sub_one_mod_two h_mb]
          decide
        · rename_i h_e
          -- nextFinite = .inf false, isFinite = false
          simp [h_m, h_e, isFinite] at h_succ_fin
  | .finite true e m, _ =>
      simp only [nextFinite] at h_succ_fin ⊢
      split
      · rename_i h_m
        simp only [mantissaLSB_finite]
        left
        omega
      · rename_i h_m
        simp only [ne_eq, not_not] at h_m
        split
        · rename_i h_e
          simp only [ne_eq] at h_e
          simp only [mantissaLSB_finite]
          left
          rw [h_m, two_pow_sub_one_mod_two h_mb]
          decide
        · rename_i h_e
          simp only [ne_eq, not_not] at h_e
          simp only [mantissaLSB_finite]
          right
          refine ⟨?_, ?_⟩ <;> omega

/-! ## Real-value monotonicity per case

Each gap-strict-lt lemma rephrased to match the exact `Fin`
construction inside `nextFinite`, avoiding `convert`-style unification
issues. -/

theorem nextFinite_value_lt_pos_within
    (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) (h_m : m.val + 1 < 2 ^ mb) :
    (.finite false e m : IEEEFloat eb mb).toRealOrZero
      < (.finite false e ⟨m.val + 1, h_m⟩ : IEEEFloat eb mb).toRealOrZero := by
  simp only [toRealOrZero_finite_eq]
  exact finiteValue_pos_within_lt e m h_m

theorem nextFinite_value_lt_pos_cross
    (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb))
    (h_m : ¬ m.val + 1 < 2 ^ mb) (h_e : e.val + 1 < 2 ^ eb - 1) :
    (.finite false e m : IEEEFloat eb mb).toRealOrZero
      < (.finite false ⟨e.val + 1, h_e⟩ ⟨0, pow_pos (by decide : 0 < 2) mb⟩
          : IEEEFloat eb mb).toRealOrZero := by
  have h_m_eq : m.val = 2 ^ mb - 1 := by have := m.isLt; omega
  have h_max : 2 ^ mb - 1 < 2 ^ mb := by have := m.isLt; omega
  have h_zero : 0 < 2 ^ mb := pow_pos (by decide) mb
  simp only [toRealOrZero_finite_eq]
  -- Replace m with ⟨2^mb - 1, h_max⟩ via congr-arg-style
  have hm_step : finiteValue (eb := eb) (mb := mb) false e m
               = finiteValue false e ⟨2 ^ mb - 1, h_max⟩ := by
    congr 1
    exact Fin.ext h_m_eq
  rw [hm_step]
  by_cases he_zero : e.val = 0
  · -- subnormal
    have he_pos : (0 : Nat) < 2 ^ eb - 1 := by rw [← he_zero]; exact e.isLt
    have he_new_pos : (1 : Nat) < 2 ^ eb - 1 := by
      have : e.val + 1 < 2 ^ eb - 1 := h_e
      rw [he_zero] at this; exact this
    have he_step1 : finiteValue (eb := eb) (mb := mb) false e ⟨2 ^ mb - 1, h_max⟩
                  = finiteValue false ⟨0, he_pos⟩ ⟨2 ^ mb - 1, h_max⟩ := by
      congr 1; exact Fin.ext he_zero
    have he_step2 : finiteValue (eb := eb) (mb := mb) false ⟨e.val + 1, h_e⟩ ⟨0, h_zero⟩
                  = finiteValue false ⟨1, he_new_pos⟩ ⟨0, h_zero⟩ := by
      congr 1; ext; show e.val + 1 = 1; omega
    rw [he_step1, he_step2]
    exact finiteValue_pos_cross_subnormal_lt he_pos he_new_pos h_max h_zero
  · -- normal
    have h_e_pos : 1 ≤ e.val := Nat.one_le_iff_ne_zero.mpr he_zero
    have he_step : finiteValue (eb := eb) (mb := mb) false e ⟨2 ^ mb - 1, h_max⟩
                 = finiteValue false ⟨e.val, e.isLt⟩ ⟨2 ^ mb - 1, h_max⟩ := rfl
    rw [he_step]
    exact finiteValue_pos_cross_normal_lt e.val h_e_pos e.isLt h_e h_max h_zero

theorem nextFinite_value_lt_neg_within
    (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) (h_m : m.val ≠ 0) :
    (.finite true e m : IEEEFloat eb mb).toRealOrZero
      < (.finite true e ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) m.isLt⟩
          : IEEEFloat eb mb).toRealOrZero := by
  have h_m_pred_lt : m.val - 1 + 1 < 2 ^ mb := by have := m.isLt; omega
  simp only [toRealOrZero_finite_eq]
  have hm_step : finiteValue (eb := eb) (mb := mb) true e m
               = finiteValue true e ⟨(m.val - 1) + 1, h_m_pred_lt⟩ := by
    congr 1
    apply Fin.ext; show m.val = (m.val - 1) + 1; omega
  rw [hm_step]
  exact finiteValue_neg_within_lt e
    ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) m.isLt⟩ h_m_pred_lt

theorem nextFinite_value_lt_neg_cross
    (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb))
    (h_m : ¬ m.val ≠ 0) (h_e : e.val ≠ 0) :
    (.finite true e m : IEEEFloat eb mb).toRealOrZero
      < (.finite true ⟨e.val - 1, lt_of_le_of_lt (Nat.sub_le e.val 1) e.isLt⟩
            ⟨2 ^ mb - 1, by have := pow_pos (by decide : 0 < 2) mb; omega⟩
          : IEEEFloat eb mb).toRealOrZero := by
  push_neg at h_m
  have h_max : 2 ^ mb - 1 < 2 ^ mb := by
    have := pow_pos (by decide : (0 : Nat) < 2) mb; omega
  have h_zero : 0 < 2 ^ mb := pow_pos (by decide) mb
  have h_e_pred_lt : e.val - 1 < 2 ^ eb - 1 :=
    lt_of_le_of_lt (Nat.sub_le _ _) e.isLt
  simp only [toRealOrZero_finite_eq]
  have hm_step : finiteValue (eb := eb) (mb := mb) true e m
               = finiteValue true e ⟨0, h_zero⟩ := by
    congr 1; exact Fin.ext h_m
  rw [hm_step]
  by_cases h_e_eq_one : e.val = 1
  · have h_e_old_lt : (1 : Nat) < 2 ^ eb - 1 := by
      have h := e.isLt; rw [h_e_eq_one] at h; exact h
    have h_e_new_lt : (0 : Nat) < 2 ^ eb - 1 := by
      have : (1 : Nat) < 2 ^ eb - 1 := h_e_old_lt; omega
    have he_step1 : finiteValue (eb := eb) (mb := mb) true e ⟨0, h_zero⟩
                  = finiteValue true ⟨1, h_e_old_lt⟩ ⟨0, h_zero⟩ := by
      congr 1; exact Fin.ext h_e_eq_one
    have he_step2 : finiteValue (eb := eb) (mb := mb) true
                      ⟨e.val - 1, h_e_pred_lt⟩ ⟨2 ^ mb - 1, h_max⟩
                  = finiteValue true ⟨0, h_e_new_lt⟩ ⟨2 ^ mb - 1, h_max⟩ := by
      congr 1; ext; show e.val - 1 = 0; omega
    rw [he_step1, he_step2]
    exact finiteValue_neg_cross_to_subnormal_lt h_e_old_lt h_e_new_lt h_max h_zero
  · have h_e_ge_2 : 2 ≤ e.val := by omega
    have he_step : finiteValue (eb := eb) (mb := mb) true e ⟨0, h_zero⟩
                 = finiteValue true ⟨e.val, e.isLt⟩ ⟨0, h_zero⟩ := rfl
    rw [he_step]
    exact finiteValue_neg_cross_to_normal_lt e.val h_e_ge_2 e.isLt h_e_pred_lt h_max h_zero

theorem nextFinite_value_eq_neg_zero
    (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb))
    (h_m : ¬ m.val ≠ 0) (h_e : ¬ e.val ≠ 0) :
    (.finite true e m : IEEEFloat eb mb).toRealOrZero = 0 ∧
    (.finite false e m : IEEEFloat eb mb).toRealOrZero = 0 := by
  push_neg at h_m h_e
  refine ⟨?_, ?_⟩
  all_goals
    simp only [toRealOrZero_finite_eq, finiteValue]
    rw [show m.val = 0 from h_m]
    simp [h_e]

theorem nextFinite_toRealOrZero_ge
    (x : IEEEFloat eb mb) (h_fin : x.isFinite = true)
    (h_succ_fin : (nextFinite x).isFinite = true) :
    x.toRealOrZero ≤ (nextFinite x).toRealOrZero := by
  match x, h_fin with
  | .finite false e m, _ =>
      simp only [nextFinite] at h_succ_fin ⊢
      split
      · rename_i h_m
        exact le_of_lt (nextFinite_value_lt_pos_within e m h_m)
      · rename_i h_m
        split
        · rename_i h_e
          exact le_of_lt (nextFinite_value_lt_pos_cross e m h_m h_e)
        · rename_i h_e
          simp [h_m, h_e, isFinite] at h_succ_fin
  | .finite true e m, _ =>
      simp only [nextFinite] at h_succ_fin ⊢
      split
      · rename_i h_m
        exact le_of_lt (nextFinite_value_lt_neg_within e m h_m)
      · rename_i h_m
        split
        · rename_i h_e
          have h_e_ne : e.val ≠ 0 := h_e
          exact le_of_lt (nextFinite_value_lt_neg_cross e m h_m h_e_ne)
        · rename_i h_e
          have ⟨h1, h2⟩ := nextFinite_value_eq_neg_zero e m h_m h_e
          rw [h1, h2]

/-! ## `finiteValue` injectivity modulo ±0

Two distinct finite encodings encode the same real value only at
`±0` (`(s, 0, 0)` for either sign).  All other encodings are
unique.

Proof structure: 4-way case split on whether each exponent is zero
(subnormal) or non-zero (normal).
  *  (subnormal, subnormal): direct algebra.
  *  (normal, normal): exponents must agree (else magnitude differs
     by ≥ factor of 2); then mantissas agree.
  *  Mixed (subnormal, normal): impossible — subnormal magnitude
     `< 2^minNormalExp`, normal magnitude `≥ 2^minNormalExp`. -/

private theorem finiteValue_subnormal_lt_two_pow_minNormalExp
    (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) (he : e.val = 0) :
    |finiteValue (eb := eb) (mb := mb) s e m| < (2 : ℝ) ^ minNormalExp eb := by
  simp only [finiteValue, he, ↓reduceIte]
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ mb := two_pow_mb_pos
  have h2zpow_pos : (0 : ℝ) < (2 : ℝ) ^ minNormalExp eb := zpow_pos (by norm_num) _
  have hm_lt : (m.val : ℝ) / (2 : ℝ) ^ mb < 1 := by
    rw [div_lt_one h2pos]
    have : (m.val : ℝ) < ((2 ^ mb : Nat) : ℝ) := by exact_mod_cast m.isLt
    convert this using 1
    push_cast; rfl
  have hm_nn : (0 : ℝ) ≤ (m.val : ℝ) / (2 : ℝ) ^ mb :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt h2pos)
  rcases s with - | -
  · -- s = false (positive)
    rw [show (if false = true then (-1 : ℝ) else 1) = 1 from rfl]
    rw [show (1 : ℝ) * (2 : ℝ) ^ minNormalExp eb * ((m.val : ℝ) / (2 : ℝ) ^ mb)
          = (2 : ℝ) ^ minNormalExp eb * ((m.val : ℝ) / (2 : ℝ) ^ mb) from by ring]
    rw [abs_of_nonneg (by positivity)]
    calc (2 : ℝ) ^ minNormalExp eb * ((m.val : ℝ) / (2 : ℝ) ^ mb)
        < (2 : ℝ) ^ minNormalExp eb * 1 :=
          mul_lt_mul_of_pos_left hm_lt h2zpow_pos
      _ = (2 : ℝ) ^ minNormalExp eb := by ring
  · -- s = true (negative)
    rw [show (if true = true then (-1 : ℝ) else 1) = -1 from rfl]
    rw [show (-1 : ℝ) * (2 : ℝ) ^ minNormalExp eb * ((m.val : ℝ) / (2 : ℝ) ^ mb)
          = -((2 : ℝ) ^ minNormalExp eb * ((m.val : ℝ) / (2 : ℝ) ^ mb)) from by ring]
    rw [abs_neg, abs_of_nonneg (by positivity)]
    calc (2 : ℝ) ^ minNormalExp eb * ((m.val : ℝ) / (2 : ℝ) ^ mb)
        < (2 : ℝ) ^ minNormalExp eb * 1 :=
          mul_lt_mul_of_pos_left hm_lt h2zpow_pos
      _ = (2 : ℝ) ^ minNormalExp eb := by ring

private theorem finiteValue_normal_abs_ge_two_pow_minNormalExp
    (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) (he : e.val ≠ 0) :
    (2 : ℝ) ^ minNormalExp eb ≤ |finiteValue (eb := eb) (mb := mb) s e m| := by
  simp only [finiteValue, he, ↓reduceIte]
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ mb := two_pow_mb_pos
  have hf_pos := finiteValue_normal_pos (s := s) (e := e) (m := m) he
  have h_e_int_ge : minNormalExp eb ≤ (e.val : Int) - bias eb := by
    rw [show minNormalExp eb = 1 - bias eb from rfl]
    have h_e_pos : 1 ≤ e.val := Nat.one_le_iff_ne_zero.mpr he
    push_cast; omega
  have h_zpow_mono : (2 : ℝ) ^ minNormalExp eb
      ≤ (2 : ℝ) ^ ((e.val : Int) - bias eb) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h_e_int_ge
  have h_factor_ge_one : (1 : ℝ) ≤ 1 + (m.val : ℝ) / (2 : ℝ) ^ mb := by
    have : (0 : ℝ) ≤ (m.val : ℝ) / (2 : ℝ) ^ mb :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt h2pos)
    linarith
  have h_main : (2 : ℝ) ^ minNormalExp eb ≤
      (2 : ℝ) ^ ((e.val : Int) - bias eb) * (1 + (m.val : ℝ) / (2 : ℝ) ^ mb) := by
    calc (2 : ℝ) ^ minNormalExp eb
        = (2 : ℝ) ^ minNormalExp eb * 1 := by ring
      _ ≤ (2 : ℝ) ^ ((e.val : Int) - bias eb) * 1 :=
          mul_le_mul_of_nonneg_right h_zpow_mono zero_le_one
      _ ≤ (2 : ℝ) ^ ((e.val : Int) - bias eb) * (1 + (m.val : ℝ) / (2 : ℝ) ^ mb) :=
          mul_le_mul_of_nonneg_left h_factor_ge_one (le_of_lt (zpow_pos (by norm_num) _))
  -- Same magnitude either sign.
  have h_abs_eq : |(if s = true then (-1 : ℝ) else 1) * (2 : ℝ) ^ ((e.val : Int) - bias eb)
                       * (1 + (m.val : ℝ) / (2 : ℝ) ^ mb)|
                = (2 : ℝ) ^ ((e.val : Int) - bias eb) * (1 + (m.val : ℝ) / (2 : ℝ) ^ mb) := by
    rcases s with - | -
    · rw [show (if false = true then (-1 : ℝ) else 1) = 1 from rfl, one_mul,
          abs_of_pos hf_pos]
    · simp only [if_true]
      rw [show (-1 : ℝ) * (2 : ℝ) ^ ((e.val : Int) - bias eb) *
                (1 + (m.val : ℝ) / (2 : ℝ) ^ mb)
            = -((2 : ℝ) ^ ((e.val : Int) - bias eb) *
                (1 + (m.val : ℝ) / (2 : ℝ) ^ mb)) from by ring,
          abs_neg, abs_of_pos hf_pos]
  rw [h_abs_eq]
  exact h_main

/-! ## `finiteValue` injectivity modulo ±0 -/

private theorem finiteValue_subnormal_abs
    (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) (he : e.val = 0) :
    |finiteValue (eb := eb) (mb := mb) s e m|
      = (2 : ℝ) ^ minNormalExp eb * ((m.val : ℝ) / (2 : ℝ) ^ mb) := by
  simp only [finiteValue, he, ↓reduceIte]
  have h2mb_pos : (0 : ℝ) < (2 : ℝ) ^ mb := two_pow_mb_pos
  have h2zpow_pos : (0 : ℝ) < (2 : ℝ) ^ minNormalExp eb := zpow_pos (by norm_num) _
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ minNormalExp eb * ((m.val : ℝ) / (2 : ℝ) ^ mb) := by
    apply mul_nonneg (le_of_lt h2zpow_pos)
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt h2mb_pos)
  rcases s with - | -
  · rw [show (if false = true then (-1 : ℝ) else 1) = 1 from rfl, one_mul,
        abs_of_nonneg hnn]
  · rw [show (if true = true then (-1 : ℝ) else 1) = -1 from rfl,
        show (-1 : ℝ) * (2 : ℝ) ^ minNormalExp eb * ((m.val : ℝ) / (2 : ℝ) ^ mb)
          = -((2 : ℝ) ^ minNormalExp eb * ((m.val : ℝ) / (2 : ℝ) ^ mb)) from by ring,
        abs_neg, abs_of_nonneg hnn]

private theorem finiteValue_normal_abs
    (s : Bool) (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) (he : e.val ≠ 0) :
    |finiteValue (eb := eb) (mb := mb) s e m|
      = (2 : ℝ) ^ ((e.val : Int) - bias eb) * (1 + (m.val : ℝ) / (2 : ℝ) ^ mb) := by
  have hf_pos := finiteValue_normal_pos (s := s) (e := e) (m := m) he
  simp only [finiteValue, he, ↓reduceIte]
  rcases s with - | -
  · rw [show (if false = true then (-1 : ℝ) else 1) = 1 from rfl, one_mul,
        abs_of_pos hf_pos]
  · rw [show (if true = true then (-1 : ℝ) else 1) = -1 from rfl,
        show (-1 : ℝ) * (2 : ℝ) ^ ((e.val : Int) - bias eb) *
              (1 + (m.val : ℝ) / (2 : ℝ) ^ mb)
          = -((2 : ℝ) ^ ((e.val : Int) - bias eb) *
              (1 + (m.val : ℝ) / (2 : ℝ) ^ mb)) from by ring,
        abs_neg, abs_of_pos hf_pos]

theorem finiteValue_inj_modulo_zero
    {s₁ s₂ : Bool} {e₁ e₂ : Fin (2 ^ eb - 1)} {m₁ m₂ : Fin (2 ^ mb)}
    (h : finiteValue (eb := eb) (mb := mb) s₁ e₁ m₁
       = finiteValue s₂ e₂ m₂) :
    (m₁.val = 0 ∧ m₂.val = 0 ∧ e₁.val = 0 ∧ e₂.val = 0) ∨
    (s₁ = s₂ ∧ e₁ = e₂ ∧ m₁ = m₂) := by
  have h_abs : |finiteValue (eb := eb) (mb := mb) s₁ e₁ m₁|
             = |finiteValue (eb := eb) (mb := mb) s₂ e₂ m₂| := by rw [h]
  have h_2pow_pos : (0 : ℝ) < (2 : ℝ) ^ minNormalExp eb := zpow_pos (by norm_num) _
  have h_2mb_pos : (0 : ℝ) < (2 : ℝ) ^ mb := two_pow_mb_pos
  by_cases he₁ : e₁.val = 0
  · by_cases he₂ : e₂.val = 0
    · rw [finiteValue_subnormal_abs s₁ e₁ m₁ he₁,
          finiteValue_subnormal_abs s₂ e₂ m₂ he₂] at h_abs
      have h_m_real : (m₁.val : ℝ) = (m₂.val : ℝ) := by
        have h1 := mul_left_cancel₀ (ne_of_gt h_2pow_pos) h_abs
        exact (div_left_inj' (ne_of_gt h_2mb_pos)).mp h1
      have h_m_eq : m₁.val = m₂.val := Nat.cast_injective h_m_real
      by_cases hm₁ : m₁.val = 0
      · left; exact ⟨hm₁, hm₁ ▸ h_m_eq.symm, he₁, he₂⟩
      · right
        refine ⟨?_, Fin.ext (he₁.trans he₂.symm), Fin.ext h_m_eq⟩
        simp only [finiteValue, he₁, he₂, ↓reduceIte] at h
        have h_factor_ne : (2 : ℝ) ^ minNormalExp eb * ((m₁.val : ℝ) / (2 : ℝ) ^ mb) ≠ 0 := by
          have hm_real_ne : (m₁.val : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm₁
          have h_div_ne : (m₁.val : ℝ) / (2 : ℝ) ^ mb ≠ 0 :=
            div_ne_zero hm_real_ne (ne_of_gt h_2mb_pos)
          exact mul_ne_zero (ne_of_gt h_2pow_pos) h_div_ne
        rw [show m₂.val = m₁.val from h_m_eq.symm] at h
        rcases s₁ with - | - <;> rcases s₂ with - | -
        · rfl
        · simp at h
          have : (2 : ℝ) ^ minNormalExp eb * ((m₁.val : ℝ) / (2 : ℝ) ^ mb) = 0 := by linarith
          exact absurd this h_factor_ne
        · simp at h
          have : (2 : ℝ) ^ minNormalExp eb * ((m₁.val : ℝ) / (2 : ℝ) ^ mb) = 0 := by linarith
          exact absurd this h_factor_ne
        · rfl
    · exfalso
      have h_lt := finiteValue_subnormal_lt_two_pow_minNormalExp s₁ e₁ m₁ he₁
      have h_ge := finiteValue_normal_abs_ge_two_pow_minNormalExp s₂ e₂ m₂ he₂
      rw [h_abs] at h_lt
      linarith
  · by_cases he₂ : e₂.val = 0
    · exfalso
      have h_ge := finiteValue_normal_abs_ge_two_pow_minNormalExp s₁ e₁ m₁ he₁
      have h_lt := finiteValue_subnormal_lt_two_pow_minNormalExp s₂ e₂ m₂ he₂
      rw [← h_abs] at h_lt
      linarith
    · rw [finiteValue_normal_abs s₁ e₁ m₁ he₁,
          finiteValue_normal_abs s₂ e₂ m₂ he₂] at h_abs
      have h_e_eq : e₁.val = e₂.val := by
        by_contra h_ne
        rcases Nat.lt_or_lt_of_ne h_ne with h_lt | h_lt
        · have h₁ := finiteValue_normal_lt_two_pow (s := s₁) e₁ m₁ he₁
          have h_zpow : (2 : ℝ) ^ ((e₁.val : Int) + 1 - bias eb)
                      ≤ (2 : ℝ) ^ ((e₂.val : Int) - bias eb) := by
            apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
            omega
          have h_factor_ge : (1 : ℝ) ≤ 1 + (m₂.val : ℝ) / (2 : ℝ) ^ mb := by
            have : (0 : ℝ) ≤ (m₂.val : ℝ) / (2 : ℝ) ^ mb :=
              div_nonneg (Nat.cast_nonneg _) (le_of_lt h_2mb_pos)
            linarith
          have h_strict :
              (2 : ℝ) ^ ((e₁.val : Int) - bias eb) * (1 + (m₁.val : ℝ) / (2 : ℝ) ^ mb)
              < (2 : ℝ) ^ ((e₂.val : Int) - bias eb) * (1 + (m₂.val : ℝ) / (2 : ℝ) ^ mb) :=
            calc _
                < (2 : ℝ) ^ ((e₁.val : Int) + 1 - bias eb) := h₁
              _ = (2 : ℝ) ^ ((e₁.val : Int) + 1 - bias eb) * 1 := by ring
              _ ≤ (2 : ℝ) ^ ((e₂.val : Int) - bias eb) * 1 :=
                  mul_le_mul_of_nonneg_right h_zpow zero_le_one
              _ ≤ _ := mul_le_mul_of_nonneg_left h_factor_ge
                  (le_of_lt (zpow_pos (by norm_num) _))
          linarith
        · have h₂ := finiteValue_normal_lt_two_pow (s := s₂) e₂ m₂ he₂
          have h_zpow : (2 : ℝ) ^ ((e₂.val : Int) + 1 - bias eb)
                      ≤ (2 : ℝ) ^ ((e₁.val : Int) - bias eb) := by
            apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
            omega
          have h_factor_ge : (1 : ℝ) ≤ 1 + (m₁.val : ℝ) / (2 : ℝ) ^ mb := by
            have : (0 : ℝ) ≤ (m₁.val : ℝ) / (2 : ℝ) ^ mb :=
              div_nonneg (Nat.cast_nonneg _) (le_of_lt h_2mb_pos)
            linarith
          have h_strict :
              (2 : ℝ) ^ ((e₂.val : Int) - bias eb) * (1 + (m₂.val : ℝ) / (2 : ℝ) ^ mb)
              < (2 : ℝ) ^ ((e₁.val : Int) - bias eb) * (1 + (m₁.val : ℝ) / (2 : ℝ) ^ mb) :=
            calc _
                < (2 : ℝ) ^ ((e₂.val : Int) + 1 - bias eb) := h₂
              _ = (2 : ℝ) ^ ((e₂.val : Int) + 1 - bias eb) * 1 := by ring
              _ ≤ (2 : ℝ) ^ ((e₁.val : Int) - bias eb) * 1 :=
                  mul_le_mul_of_nonneg_right h_zpow zero_le_one
              _ ≤ _ := mul_le_mul_of_nonneg_left h_factor_ge
                  (le_of_lt (zpow_pos (by norm_num) _))
          linarith
      rw [show ((e₂.val : Int) - bias eb) = (e₁.val : Int) - bias eb from by
          rw [h_e_eq]] at h_abs
      have h_2zpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((e₁.val : Int) - bias eb) :=
        zpow_pos (by norm_num) _
      have h_factor_eq : 1 + (m₁.val : ℝ) / (2 : ℝ) ^ mb
                       = 1 + (m₂.val : ℝ) / (2 : ℝ) ^ mb :=
        mul_left_cancel₀ (ne_of_gt h_2zpow_pos) h_abs
      have h_m_real : (m₁.val : ℝ) = (m₂.val : ℝ) := by
        have h1 : (m₁.val : ℝ) / (2 : ℝ) ^ mb = (m₂.val : ℝ) / (2 : ℝ) ^ mb := by linarith
        exact (div_left_inj' (ne_of_gt h_2mb_pos)).mp h1
      have h_m_eq : m₁.val = m₂.val := Nat.cast_injective h_m_real
      right
      refine ⟨?_, Fin.ext h_e_eq, Fin.ext h_m_eq⟩
      simp only [finiteValue, he₁, he₂, ↓reduceIte] at h
      rw [h_e_eq, h_m_eq] at h
      have h_mag_pos := finiteValue_normal_pos (s := s₂) (e := e₂) (m := m₂) he₂
      rcases s₁ with - | - <;> rcases s₂ with - | -
      · rfl
      · simp at h; linarith
      · simp at h; linarith
      · rfl

/-! ## Deferred theorems

The mathematically interesting properties of `ulp`, `nextFinite`,
`prevFinite` — the ones theorems about RNE tie-break and half-ULP
bounds depend on — are stated below as section headers for future
work.  No sorry, no axiom: the *proofs* land in their own commits
once the bit-level case-analysis machinery is fleshed out.

  *  **Real-value monotonicity**:
       `x.isFinite → (nextFinite x).toRealOrZero ≥ x.toRealOrZero`
       (with equality only for `−0 → +0`).  Mirror for `prevFinite`.

  *  **Encoding adjacency**:
       For finite `x ≠ +∞` with `(nextFinite x).isFinite`,
       `(nextFinite x).toRealOrZero - x.toRealOrZero ∈ {0, ulp x}`
       (the `0` arising only at the `−0 → +0` step).

  *  **No representable strictly between**:
       For finite `x` with `nextFinite x` finite,
       `∀ y finite, x.toRealOrZero < y.toRealOrZero <
         (nextFinite x).toRealOrZero → False`.

  *  **Mantissa-LSB alternation**:
       For finite `x` with `nextFinite x` finite and not the
       `−0 → +0` step, `x.mantissaLSB ≠ (nextFinite x).mantissaLSB`.
       At the `−0 → +0` step both are zero (even).

These four together are exactly the structural input to the
RNE-existence proof in `IEEEFloat.RoundExistence` (next commit). -/

/-! ## Helpers for encoding-adjacency

`finiteValue` is strictly monotone within the positive (and within
the negative) strata as `(e, m)` increases lex. -/

/-- Within positive stratum, mantissa increase ↔ value increase. -/
private theorem finiteValue_pos_mantissa_strict_mono
    (e : Fin (2 ^ eb - 1)) (m₁ m₂ : Fin (2 ^ mb)) (h : m₁.val < m₂.val) :
    finiteValue (eb := eb) (mb := mb) false e m₁
      < finiteValue (eb := eb) (mb := mb) false e m₂ := by
  simp only [finiteValue, show (if false = true then (-1 : ℝ) else 1) = 1 from rfl, one_mul]
  have h2mb_pos : (0 : ℝ) < (2 : ℝ) ^ mb := two_pow_mb_pos
  have h_m_real : (m₁.val : ℝ) < (m₂.val : ℝ) := by exact_mod_cast h
  have h_div_lt : (m₁.val : ℝ) / (2 : ℝ) ^ mb < (m₂.val : ℝ) / (2 : ℝ) ^ mb :=
    (div_lt_div_iff_of_pos_right h2mb_pos).mpr h_m_real
  by_cases he : e.val = 0
  · simp only [he, ↓reduceIte]
    have h2zpow_pos : (0 : ℝ) < (2 : ℝ) ^ minNormalExp eb := zpow_pos (by norm_num) _
    exact mul_lt_mul_of_pos_left h_div_lt h2zpow_pos
  · simp only [he, ↓reduceIte]
    have h2zpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((e.val : Int) - bias eb) :=
      zpow_pos (by norm_num) _
    have : (1 : ℝ) + (m₁.val : ℝ) / (2 : ℝ) ^ mb
         < 1 + (m₂.val : ℝ) / (2 : ℝ) ^ mb := by linarith
    exact mul_lt_mul_of_pos_left this h2zpow_pos

/-- Across positive strata: smaller exponent → strictly smaller value.
    Precondition: `e₁.val < e₂.val` (so different strata). -/
private theorem finiteValue_pos_exp_strict_mono
    {e₁ e₂ : Fin (2 ^ eb - 1)} (m₁ m₂ : Fin (2 ^ mb)) (h_e : e₁.val < e₂.val) :
    finiteValue (eb := eb) (mb := mb) false e₁ m₁
      < finiteValue (eb := eb) (mb := mb) false e₂ m₂ := by
  -- LHS < 2^(e₁+1 - bias) (or 2^minNormalExp for subnormal); RHS ≥ 2^(e₂ - bias) (≥ 2^minNormalExp for normal)
  -- Key fact: 2^(e₁+1 - bias) ≤ 2^(e₂ - bias) for e₁ + 1 ≤ e₂, i.e., e₁ < e₂.
  have h2mb_pos : (0 : ℝ) < (2 : ℝ) ^ mb := two_pow_mb_pos
  by_cases he₂ : e₂.val = 0
  · -- e₂ = 0 → subnormal RHS, but e₁ < e₂ = 0 impossible since e₁ ≥ 0
    omega
  · have he₂_pos : 1 ≤ e₂.val := Nat.one_le_iff_ne_zero.mpr he₂
    -- RHS magnitude ≥ 2^(e₂ - bias)
    have h_rhs_pos : (0 : ℝ) < finiteValue (eb := eb) (mb := mb) false e₂ m₂ := by
      simp only [finiteValue, he₂, ↓reduceIte,
                 show (if false = true then (-1 : ℝ) else 1) = 1 from rfl, one_mul]
      exact finiteValue_normal_pos (s := false) (e := e₂) (m := m₂) he₂
    have h_rhs_ge : (2 : ℝ) ^ ((e₂.val : Int) - bias eb)
                  ≤ finiteValue (eb := eb) (mb := mb) false e₂ m₂ := by
      simp only [finiteValue, he₂, ↓reduceIte,
                 show (if false = true then (-1 : ℝ) else 1) = 1 from rfl, one_mul]
      have h_factor : (1 : ℝ) ≤ 1 + (m₂.val : ℝ) / (2 : ℝ) ^ mb := by
        have : (0 : ℝ) ≤ (m₂.val : ℝ) / (2 : ℝ) ^ mb :=
          div_nonneg (Nat.cast_nonneg _) (le_of_lt h2mb_pos)
        linarith
      have h2zpow : (0 : ℝ) < (2 : ℝ) ^ ((e₂.val : Int) - bias eb) :=
        zpow_pos (by norm_num) _
      calc (2 : ℝ) ^ ((e₂.val : Int) - bias eb)
          = (2 : ℝ) ^ ((e₂.val : Int) - bias eb) * 1 := by ring
        _ ≤ (2 : ℝ) ^ ((e₂.val : Int) - bias eb) * (1 + (m₂.val : ℝ) / (2 : ℝ) ^ mb) :=
            mul_le_mul_of_nonneg_left h_factor (le_of_lt h2zpow)
    -- LHS magnitude < 2^(e₁ + 1 - bias) (normal or subnormal sub-case)
    by_cases he₁ : e₁.val = 0
    · -- LHS subnormal
      have h_lhs_lt_two_pow : finiteValue (eb := eb) (mb := mb) false e₁ m₁
                            < (2 : ℝ) ^ minNormalExp eb := by
        simp only [finiteValue, he₁, ↓reduceIte,
                   show (if false = true then (-1 : ℝ) else 1) = 1 from rfl, one_mul]
        have hm_lt_one : (m₁.val : ℝ) / (2 : ℝ) ^ mb < 1 := by
          rw [div_lt_one h2mb_pos]
          have : (m₁.val : ℝ) < ((2 ^ mb : Nat) : ℝ) := by exact_mod_cast m₁.isLt
          convert this using 1; push_cast; rfl
        have h2zpow : (0 : ℝ) < (2 : ℝ) ^ minNormalExp eb := zpow_pos (by norm_num) _
        calc (2 : ℝ) ^ minNormalExp eb * ((m₁.val : ℝ) / (2 : ℝ) ^ mb)
            < (2 : ℝ) ^ minNormalExp eb * 1 :=
              mul_lt_mul_of_pos_left hm_lt_one h2zpow
          _ = (2 : ℝ) ^ minNormalExp eb := by ring
      have h_minNormalExp_le : (2 : ℝ) ^ minNormalExp eb
                             ≤ (2 : ℝ) ^ ((e₂.val : Int) - bias eb) := by
        apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        rw [show minNormalExp eb = 1 - bias eb from rfl]
        push_cast; omega
      linarith
    · -- LHS normal
      have h_lhs_lt_next : finiteValue (eb := eb) (mb := mb) false e₁ m₁
                         < (2 : ℝ) ^ ((e₁.val : Int) + 1 - bias eb) := by
        simp only [show (if false = true then (-1 : ℝ) else 1) = 1 from rfl, one_mul,
                   finiteValue, he₁, ↓reduceIte]
        exact finiteValue_normal_lt_two_pow (s := false) e₁ m₁ he₁
      have h_zpow_le : (2 : ℝ) ^ ((e₁.val : Int) + 1 - bias eb)
                     ≤ (2 : ℝ) ^ ((e₂.val : Int) - bias eb) := by
        apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        omega
      linarith

/-- Trichotomy for positive finites: comparison of `(e, m)` lex matches
    real-value order (with equality at the same encoding). -/
theorem finiteValue_pos_lt_iff
    (e₁ e₂ : Fin (2 ^ eb - 1)) (m₁ m₂ : Fin (2 ^ mb)) :
    finiteValue (eb := eb) (mb := mb) false e₁ m₁
      < finiteValue (eb := eb) (mb := mb) false e₂ m₂
    ↔ e₁.val < e₂.val ∨ (e₁.val = e₂.val ∧ m₁.val < m₂.val) := by
  constructor
  · intro h
    by_contra h_ne
    push_neg at h_ne
    obtain ⟨h_e_ge, h_m_ge⟩ := h_ne
    -- h_e_ge : e₂.val ≤ e₁.val (from push_neg of ¬ e₁ < e₂).
    rcases lt_or_eq_of_le h_e_ge with h_e_lt | h_e_eq
    · have := finiteValue_pos_exp_strict_mono (e₁ := e₂) (e₂ := e₁) m₂ m₁ h_e_lt
      linarith
    · rcases lt_or_eq_of_le (h_m_ge h_e_eq.symm) with h_m_lt | h_m_eq
      · have h_e_eq' : e₁ = e₂ := Fin.ext h_e_eq.symm
        rw [h_e_eq'] at h
        have := finiteValue_pos_mantissa_strict_mono (eb := eb) (mb := mb) e₂ m₂ m₁ h_m_lt
        linarith
      · have h_e_eq' : e₁ = e₂ := Fin.ext h_e_eq.symm
        have h_m_eq' : m₁ = m₂ := Fin.ext h_m_eq.symm
        rw [h_e_eq', h_m_eq'] at h
        exact lt_irrefl _ h
  · intro h
    rcases h with h_e_lt | ⟨h_e_eq, h_m_lt⟩
    · exact finiteValue_pos_exp_strict_mono m₁ m₂ h_e_lt
    · have h_e_eq' : e₁ = e₂ := Fin.ext h_e_eq
      rw [h_e_eq']
      exact finiteValue_pos_mantissa_strict_mono e₂ m₁ m₂ h_m_lt

/-! ## Negative-finite trichotomy (mirror of positive) -/

/-- Within negative stratum, mantissa increase ↔ value DECREASE
    (more-negative magnitude). -/
private theorem finiteValue_neg_mantissa_strict_anti
    (e : Fin (2 ^ eb - 1)) (m₁ m₂ : Fin (2 ^ mb)) (h : m₁.val < m₂.val) :
    finiteValue (eb := eb) (mb := mb) true e m₂
      < finiteValue (eb := eb) (mb := mb) true e m₁ := by
  have hpos := finiteValue_pos_mantissa_strict_mono (eb := eb) (mb := mb) e m₁ m₂ h
  -- finiteValue true e m = - (positive version with same e, m)
  -- (using simp on finiteValue under sign true)
  simp only [finiteValue, show (if true = true then (-1 : ℝ) else 1) = -1 from rfl] at *
  simp only [show (if false = true then (-1 : ℝ) else 1) = 1 from rfl, one_mul] at hpos
  by_cases he : e.val = 0
  · simp only [he, ↓reduceIte] at hpos ⊢
    linarith
  · simp only [he, ↓reduceIte] at hpos ⊢
    linarith

/-- Across negative strata: smaller exponent → strictly LARGER value
    (less-negative magnitude). -/
private theorem finiteValue_neg_exp_strict_anti
    {e₁ e₂ : Fin (2 ^ eb - 1)} (m₁ m₂ : Fin (2 ^ mb)) (h_e : e₁.val < e₂.val) :
    finiteValue (eb := eb) (mb := mb) true e₂ m₂
      < finiteValue (eb := eb) (mb := mb) true e₁ m₁ := by
  have hpos := finiteValue_pos_exp_strict_mono (e₁ := e₁) (e₂ := e₂) m₁ m₂ h_e
  simp only [finiteValue, show (if true = true then (-1 : ℝ) else 1) = -1 from rfl] at *
  simp only [show (if false = true then (-1 : ℝ) else 1) = 1 from rfl, one_mul] at hpos
  by_cases he₂ : e₂.val = 0
  · omega
  · have he₂_pos : 1 ≤ e₂.val := Nat.one_le_iff_ne_zero.mpr he₂
    by_cases he₁ : e₁.val = 0
    · simp only [he₁, he₂, ↓reduceIte] at hpos ⊢
      linarith
    · simp only [he₁, he₂, ↓reduceIte] at hpos ⊢
      linarith

/-! ## Encoding-adjacency: no finite rep strictly between `x` and `nextFinite x`

This is the key structural fact for RNE: for any finite `y` with
finite `nextFinite y`, no finite `z` satisfies
`y.value < z.value < (nextFinite y).value`.

Proved by case analysis on `nextFinite y`'s output. -/

/-- Helper: positive value > 0 (when nontrivial). -/
theorem finiteValue_pos_nonneg
    (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    0 ≤ finiteValue (eb := eb) (mb := mb) false e m := by
  simp only [finiteValue, show (if false = true then (-1 : ℝ) else 1) = 1 from rfl, one_mul]
  have h2mb_pos : (0 : ℝ) < (2 : ℝ) ^ mb := two_pow_mb_pos
  have hm_nn : (0 : ℝ) ≤ (m.val : ℝ) / (2 : ℝ) ^ mb :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt h2mb_pos)
  by_cases he : e.val = 0
  · simp only [he, ↓reduceIte]
    have h2zpow : (0 : ℝ) < (2 : ℝ) ^ minNormalExp eb := zpow_pos (by norm_num) _
    exact mul_nonneg (le_of_lt h2zpow) hm_nn
  · simp only [he, ↓reduceIte]
    exact le_of_lt (finiteValue_normal_pos (s := false) (e := e) (m := m) he)

/-- Helper: negative value ≤ 0. -/
theorem finiteValue_neg_nonpos
    (e : Fin (2 ^ eb - 1)) (m : Fin (2 ^ mb)) :
    finiteValue (eb := eb) (mb := mb) true e m ≤ 0 := by
  have hpos := finiteValue_pos_nonneg (eb := eb) (mb := mb) e m
  simp only [finiteValue, show (if true = true then (-1 : ℝ) else 1) = -1 from rfl] at *
  simp only [show (if false = true then (-1 : ℝ) else 1) = 1 from rfl, one_mul] at hpos
  by_cases he : e.val = 0
  · simp only [he, ↓reduceIte] at hpos ⊢
    linarith
  · simp only [he, ↓reduceIte] at hpos ⊢
    linarith

/-- Encoding-adjacency: for finite `y` with finite `nextFinite y`, no
    finite `z` has its real value strictly between `y` and `nextFinite y`. -/
theorem nextFinite_encoding_adjacent
    (y : IEEEFloat eb mb) (h_fin : y.isFinite = true)
    (h_succ_fin : (nextFinite y).isFinite = true)
    (z : IEEEFloat eb mb) (hz_fin : z.isFinite = true)
    (hz_gt : y.toRealOrZero < z.toRealOrZero) :
    (nextFinite y).toRealOrZero ≤ z.toRealOrZero := by
  match y, h_fin, z, hz_fin with
  | .finite false e_y m_y, _, .finite s_z e_z m_z, _ =>
      -- Two cases on the sign of z.
      simp only [toRealOrZero_finite_eq] at hz_gt ⊢
      rcases s_z with - | -
      · -- z is positive: use trichotomy
        have h_tri := (finiteValue_pos_lt_iff e_y e_z m_y m_z).mp hz_gt
        -- nextFinite y is one of three forms based on (m_y + 1 < 2^mb, e_y + 1 < 2^eb - 1)
        simp only [nextFinite] at h_succ_fin ⊢
        split
        · rename_i h_m
          simp only [toRealOrZero_finite_eq]
          rcases h_tri with h_e_lt | ⟨h_e_eq, h_m_lt⟩
          · -- e_z > e_y: z is in higher stratum, value ≥ next
            apply le_of_lt
            apply finiteValue_pos_exp_strict_mono _ _ h_e_lt
          · -- e_z = e_y, m_z > m_y. Since m_y + 1 ≤ m_z:
            have h_m_ge : m_y.val + 1 ≤ m_z.val := h_m_lt
            rcases lt_or_eq_of_le h_m_ge with h_m_lt' | h_m_eq'
            · apply le_of_lt
              have h_e_eq' : (⟨m_y.val + 1, h_m⟩ : Fin (2 ^ mb)).val < m_z.val := h_m_lt'
              have h_eq_e : e_y = e_z := Fin.ext h_e_eq
              rw [h_eq_e]
              exact finiteValue_pos_mantissa_strict_mono e_z ⟨m_y.val + 1, h_m⟩ m_z h_e_eq'
            · -- m_z = m_y + 1: equal value
              have h_eq_e : e_y = e_z := Fin.ext h_e_eq
              have h_eq_m : (⟨m_y.val + 1, h_m⟩ : Fin (2 ^ mb)) = m_z := Fin.ext h_m_eq'
              rw [h_eq_e, h_eq_m]
        · rename_i h_m
          split
          · rename_i h_e
            simp only [toRealOrZero_finite_eq]
            rcases h_tri with h_e_lt | ⟨h_e_eq, h_m_lt⟩
            · -- e_z > e_y. We need (nextFinite y).value ≤ z.value where nextFinite y = (false, e_y+1, 0).
              -- z is at exponent e_z > e_y, so e_z ≥ e_y + 1.
              have h_e_ge : e_y.val + 1 ≤ e_z.val := h_e_lt
              rcases lt_or_eq_of_le h_e_ge with h_e_lt' | h_e_eq'
              · apply le_of_lt
                have h_zero : 0 < 2 ^ mb := pow_pos (by decide) mb
                have h_e_lt'' : (⟨e_y.val + 1, h_e⟩ : Fin (2 ^ eb - 1)).val < e_z.val := h_e_lt'
                exact finiteValue_pos_exp_strict_mono ⟨0, h_zero⟩ m_z h_e_lt''
              · -- e_z = e_y + 1: same exponent as nextFinite. Compare mantissas.
                have h_zero : 0 < 2 ^ mb := pow_pos (by decide) mb
                have h_eq_e : (⟨e_y.val + 1, h_e⟩ : Fin (2 ^ eb - 1)) = e_z := Fin.ext h_e_eq'
                rw [h_eq_e]
                rcases Nat.eq_zero_or_pos m_z.val with h_mz_zero | h_mz_pos
                · -- m_z = 0: equal value
                  have : (⟨0, h_zero⟩ : Fin (2 ^ mb)) = m_z := Fin.ext h_mz_zero.symm
                  rw [this]
                · apply le_of_lt
                  exact finiteValue_pos_mantissa_strict_mono e_z ⟨0, h_zero⟩ m_z h_mz_pos
            · -- e_z = e_y, m_z > m_y. But m_y + 1 ≥ 2^mb means m_y = 2^mb - 1, so m_z > 2^mb - 1, impossible.
              push_neg at h_m
              have h_m_y : m_y.val = 2 ^ mb - 1 := by have := m_y.isLt; omega
              have : m_z.val < 2 ^ mb := m_z.isLt
              omega
          · rename_i h_e
            -- nextFinite y = .inf false (overflow), but h_succ_fin says it's finite — contradiction.
            simp [h_m, h_e, isFinite] at h_succ_fin
      · -- z is negative: z.value ≤ 0. But y is positive, y.value ≥ 0.
        --  z.value > y.value means z.value > y.value ≥ 0, so z.value > 0. But z.value ≤ 0. Contradiction.
        exfalso
        have h_z_nonpos := finiteValue_neg_nonpos (eb := eb) (mb := mb) e_z m_z
        have h_y_nn := finiteValue_pos_nonneg (eb := eb) (mb := mb) e_y m_y
        linarith
  | .finite true e_y m_y, _, .finite s_z e_z m_z, _ =>
      simp only [toRealOrZero_finite_eq] at hz_gt ⊢
      rcases s_z with - | -
      · -- z is positive: z.value ≥ 0 ≥ y.value (negative or zero). hz_gt holds trivially.
        -- nextFinite y is either (true, ...) or (false, 0, 0) = +0.
        -- In all sub-cases, (nextFinite y).value ≤ 0 ≤ z.value.
        simp only [nextFinite]
        split
        · simp only [toRealOrZero_finite_eq]
          have h_succ_nonpos := finiteValue_neg_nonpos (eb := eb) (mb := mb) e_y
            ⟨m_y.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) m_y.isLt⟩
          have h_z_nn := finiteValue_pos_nonneg (eb := eb) (mb := mb) e_z m_z
          linarith
        · split
          · simp only [toRealOrZero_finite_eq]
            have h_succ_nonpos := finiteValue_neg_nonpos (eb := eb) (mb := mb)
              ⟨e_y.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) e_y.isLt⟩
              ⟨2 ^ mb - 1, by have := pow_pos (by decide : 0 < 2) mb; omega⟩
            have h_z_nn := finiteValue_pos_nonneg (eb := eb) (mb := mb) e_z m_z
            linarith
          · simp only [toRealOrZero_finite_eq]
            have h_z_nn := finiteValue_pos_nonneg (eb := eb) (mb := mb) e_z m_z
            rename_i h_m_y_zero h_e_y_zero
            push_neg at h_m_y_zero h_e_y_zero
            have h_e_lt : (0 : Nat) < 2 ^ eb - 1 := h_e_y_zero ▸ e_y.isLt
            have h_m_lt : (0 : Nat) < 2 ^ mb := h_m_y_zero ▸ m_y.isLt
            have he_y_eq : e_y = ⟨0, h_e_lt⟩ := Fin.ext h_e_y_zero
            have hm_y_eq : m_y = ⟨0, h_m_lt⟩ := Fin.ext h_m_y_zero
            rw [he_y_eq, hm_y_eq]
            simp only [finiteValue_zero_pos]
            exact h_z_nn
      · -- both negative: use trichotomy (negative version)
        -- finiteValue true e_y m_y < finiteValue true e_z m_z
        -- This is equivalent to: positive(e_z, m_z) < positive(e_y, m_y), i.e., (e_z, m_z) <_lex (e_y, m_y).
        -- Want: (nextFinite y).value ≤ z.value.
        simp only [nextFinite]
        split
        · -- m_y ≠ 0: nextFinite y = (true, e_y, m_y - 1)
          rename_i h_m_y
          simp only [toRealOrZero_finite_eq]
          -- z.value > y.value means: -|z| > -|y| iff |z| < |y|.
          -- Need: (nextFinite y).value ≤ z.value, i.e., -|nextFinite y| ≤ -|z| iff |z| ≤ |nextFinite y|.
          -- nextFinite y has |nextFinite y| = |y| - ulp.
          -- |z| < |y| means |z| ≤ |y| - ulp_some. Need |z| ≤ |y| - 1ulp = |nextFinite y|.
          -- Use trichotomy in positive form.
          have h_pos_lt : finiteValue (eb := eb) (mb := mb) false e_z m_z
                       < finiteValue (eb := eb) (mb := mb) false e_y m_y := by
            -- finiteValue true e m = -finiteValue false e m
            simp only [finiteValue,
                       show (if true = true then (-1 : ℝ) else 1) = -1 from rfl,
                       show (if false = true then (-1 : ℝ) else 1) = 1 from rfl,
                       one_mul] at hz_gt ⊢
            by_cases he_y : e_y.val = 0 <;> by_cases he_z : e_z.val = 0 <;>
              simp_all <;> linarith
          have h_tri := (finiteValue_pos_lt_iff e_z e_y m_z m_y).mp h_pos_lt
          rcases h_tri with h_e_lt | ⟨h_e_eq, h_m_lt⟩
          · -- e_z < e_y: by neg trichotomy z < (true, e_y, anything in stratum) < nextFinite y
            apply le_of_lt
            apply finiteValue_neg_exp_strict_anti _ _ h_e_lt
          · -- e_z = e_y, m_z < m_y. m_z ≤ m_y - 1.
            have h_e_eq_fin : e_z = e_y := Fin.ext h_e_eq
            rw [h_e_eq_fin]
            have h_m_le : m_z.val ≤ m_y.val - 1 := by
              have h_m_y_pos : 1 ≤ m_y.val := Nat.one_le_iff_ne_zero.mpr h_m_y
              omega
            rcases lt_or_eq_of_le h_m_le with h_m_lt' | h_m_eq'
            · apply le_of_lt
              -- (true, e_y, m_y - 1).value > (true, e_y, m_z).value when m_z < m_y - 1
              exact finiteValue_neg_mantissa_strict_anti e_y m_z
                ⟨m_y.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) m_y.isLt⟩ h_m_lt'
            · have hm_eq_fin : m_z = ⟨m_y.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) m_y.isLt⟩ :=
                Fin.ext h_m_eq'
              rw [hm_eq_fin]
        · split
          · -- m_y = 0, e_y ≠ 0: nextFinite y = (true, e_y - 1, 2^mb - 1)
            rename_i h_m_y h_e_y
            push_neg at h_m_y
            simp only [ne_eq] at h_e_y
            simp only [toRealOrZero_finite_eq]
            have h_pos_lt : finiteValue (eb := eb) (mb := mb) false e_z m_z
                         < finiteValue (eb := eb) (mb := mb) false e_y m_y := by
              simp only [finiteValue,
                         show (if true = true then (-1 : ℝ) else 1) = -1 from rfl,
                         show (if false = true then (-1 : ℝ) else 1) = 1 from rfl,
                         one_mul] at hz_gt ⊢
              by_cases he_y : e_y.val = 0 <;> by_cases he_z : e_z.val = 0 <;>
                simp_all <;> linarith
            have h_tri := (finiteValue_pos_lt_iff e_z e_y m_z m_y).mp h_pos_lt
            rcases h_tri with h_e_lt | ⟨h_e_eq, h_m_lt⟩
            · -- e_z < e_y. Need: (true, e_y - 1, 2^mb - 1).value ≤ z.value.
              -- That is: |true, e_y - 1, 2^mb - 1| ≥ |z|.
              -- |true, e_y - 1, 2^mb - 1| has positive form (false, e_y - 1, 2^mb - 1).
              have h_e_le : e_z.val ≤ e_y.val - 1 := by
                have h_e_y_pos : 1 ≤ e_y.val := Nat.one_le_iff_ne_zero.mpr h_e_y
                omega
              have h_e_pred_lt : e_y.val - 1 < 2 ^ eb - 1 :=
                lt_of_le_of_lt (Nat.sub_le _ _) e_y.isLt
              rcases lt_or_eq_of_le h_e_le with h_e_lt' | h_e_eq'
              · apply le_of_lt
                have : (⟨e_y.val - 1, h_e_pred_lt⟩ : Fin (2 ^ eb - 1)).val > e_z.val := h_e_lt'
                exact finiteValue_neg_exp_strict_anti m_z _ h_e_lt'
              · -- e_z = e_y - 1: same exponent as nextFinite. Compare mantissas.
                have h_e_eq_fin : e_z = ⟨e_y.val - 1, h_e_pred_lt⟩ := Fin.ext h_e_eq'
                rw [h_e_eq_fin]
                have h_max : 2 ^ mb - 1 < 2 ^ mb := by
                  have := pow_pos (by decide : (0 : Nat) < 2) mb; omega
                have h_m_le : m_z.val ≤ 2 ^ mb - 1 := by
                  have := m_z.isLt; omega
                rcases lt_or_eq_of_le h_m_le with h_m_lt' | h_m_eq'
                · apply le_of_lt
                  exact finiteValue_neg_mantissa_strict_anti _ m_z ⟨2 ^ mb - 1, h_max⟩ h_m_lt'
                · have hm_eq_fin : m_z = ⟨2 ^ mb - 1, h_max⟩ := Fin.ext h_m_eq'
                  rw [hm_eq_fin]
            · -- e_z = e_y, m_z < m_y = 0: impossible
              omega
          · rename_i h_m_y h_e_y
            push_neg at h_m_y h_e_y
            simp only [toRealOrZero_finite_eq]
            exfalso
            have h_e_lt : (0 : Nat) < 2 ^ eb - 1 := h_e_y ▸ e_y.isLt
            have h_m_lt : (0 : Nat) < 2 ^ mb := h_m_y ▸ m_y.isLt
            have he_y_eq : e_y = ⟨0, h_e_lt⟩ := Fin.ext h_e_y
            have hm_y_eq : m_y = ⟨0, h_m_lt⟩ := Fin.ext h_m_y
            rw [he_y_eq, hm_y_eq] at hz_gt
            simp only [finiteValue_zero_neg] at hz_gt
            have : finiteValue (eb := eb) (mb := mb) true e_z m_z ≤ 0 :=
              finiteValue_neg_nonpos e_z m_z
            linarith

end IEEEFloat
