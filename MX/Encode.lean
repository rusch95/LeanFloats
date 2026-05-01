import Mathlib.Data.Vector.Defs
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import MX.Block
import MX.Decode
import MX.Round

/-! # Encoding `Vector ℝ K → MXBlock K`

The OCP MX specification describes encoding a vector of K reals into
an MXBlock as:

  1. Choose a shared E8M0 scale `s` (typically the smallest power of
     two such that all `|v[i]| / s ≤ 6`).
  2. Round each `v[i] / s` to the nearest E2M1 (ties to even).

This module provides:

  *  `encodeWithScale v s` — the parametric encoder, given an explicit
     scale.  Useful as the inner step.
  *  Roundtrip lemmas relating `decodeAt (encodeWithScale v s) i` to
     `s · roundRNE(v[i] / s)`.

Choosing the scale optimally requires computing `⌈log₂(max |v|/6)⌉`,
which in Lean involves `Real.log`-based reasoning.  We defer
`chooseScale` to a later layer; here we develop the parametric
encoder so callers can supply their own scale.
-/

namespace MX
namespace MXBlock

open E2M1 (roundRNE)

variable {K : Nat}

/-- Encode `v : List.Vector ℝ K` with a chosen E8M0 scale.  Each
    element is divided by the scale's real value and rounded to
    nearest-even into E2M1.

    If the scale is NaN, `toRealOrZero` is `0`, so every element
    becomes `roundRNE (v[i] / 0) = roundRNE 0 = +0`.  The block then
    has a NaN scale and decodes element-wise to `none` — NaN-tagged. -/
noncomputable def encodeWithScale
    (v : List.Vector ℝ K) (s : E8M0) : MXBlock K where
  scale := s
  elements := List.Vector.ofFn fun i => roundRNE ((v.get i) / s.toRealOrZero)

@[simp] theorem encodeWithScale_scale (v : List.Vector ℝ K) (s : E8M0) :
    (encodeWithScale v s).scale = s := rfl

@[simp] theorem encodeWithScale_elements_get
    (v : List.Vector ℝ K) (s : E8M0) (i : Fin K) :
    (encodeWithScale v s).elements.get i = roundRNE ((v.get i) / s.toRealOrZero) := by
  simp [encodeWithScale, List.Vector.get_ofFn]

/-! ## Decoding-after-encoding

When the scale is not NaN, the decoded value of element `i` factors
through the rounded scaled value. -/

theorem decodeAt_encodeWithScale (v : List.Vector ℝ K) (s : E8M0) (i : Fin K)
    (hns : s.isNaN = false) :
    (encodeWithScale v s).decodeAt i =
      some (s.toRealOrZero * (roundRNE ((v.get i) / s.toRealOrZero)).toReal) := by
  rw [decodeAt_finite _ (by simpa [isNaN] using hns)]
  simp

/-- When the scale is non-NaN, its `toRealOrZero` is strictly positive. -/
theorem toRealOrZero_pos (s : E8M0) (hns : s.isNaN = false) :
    0 < s.toRealOrZero := by
  have h_ne : s.raw ≠ E8M0.nanRaw := by
    intro h
    simp [E8M0.isNaN, h] at hns
  unfold E8M0.toRealOrZero
  rw [if_neg h_ne]
  exact zpow_pos (by norm_num) _

/-- When the scale is non-NaN, each decoded element is `s.toRealOrZero`
    times the rounded scaled value, with `s.toRealOrZero > 0`. -/
theorem decodeAt_encodeWithScale_pos (v : List.Vector ℝ K) (s : E8M0) (i : Fin K)
    (hns : s.isNaN = false) :
    0 < s.toRealOrZero ∧
    (encodeWithScale v s).decodeAt i =
      some (s.toRealOrZero * (roundRNE ((v.get i) / s.toRealOrZero)).toReal) :=
  ⟨toRealOrZero_pos s hns, decodeAt_encodeWithScale v s i hns⟩

/-! ## All-zero encoding

Encoding the zero vector with any non-NaN scale yields a block that
decodes to all zeros. -/

/-- `roundRNE 0 = +0` (any saturating value would have to be `±6`,
    but `0 < overflowBoundary`, and `0` is itself representable with
    distance 0). -/
theorem roundRNE_zero_toReal : (roundRNE (0 : ℝ)).toReal = 0 := by
  have h := E2M1.roundRNE_isRNE 0
  -- `IsRoundedToNearestEven 0 (roundRNE 0)`
  have hover : ¬ E2M1.overflowBoundary ≤ |(0 : ℝ)| := by
    rw [abs_zero]; unfold E2M1.overflowBoundary; norm_num
  have hin : |(0 : ℝ)| < E2M1.overflowBoundary := by
    rw [abs_zero]; unfold E2M1.overflowBoundary; norm_num
  have ⟨hmin, _⟩ := h.2 hin
  -- The roundRNE 0 must be at distance 0 (since +0 is at distance 0).
  have hpz : |((⟨false, 0, 0⟩ : E2M1)).toReal - 0| = 0 := by
    rw [E2M1.toReal_pos_zero]; simp
  have h_le : |(roundRNE 0).toReal - 0| ≤ 0 := by
    have := hmin ⟨false, 0, 0⟩
    rw [hpz] at this
    exact this
  have h_eq : |(roundRNE 0).toReal - 0| = 0 := le_antisymm h_le (abs_nonneg _)
  have : (roundRNE 0).toReal - 0 = 0 := abs_eq_zero.mp h_eq
  linarith

theorem encodeWithScale_zero_decodeAt (s : E8M0) (i : Fin K)
    (hns : s.isNaN = false) :
    (encodeWithScale (List.Vector.replicate K (0 : ℝ)) s).decodeAt i = some 0 := by
  rw [decodeAt_encodeWithScale _ s i hns]
  congr 1
  have hsv_pos := toRealOrZero_pos s hns
  have hget : (List.Vector.replicate K (0 : ℝ)).get i = 0 :=
    List.Vector.get_replicate _ _
  rw [hget, zero_div, roundRNE_zero_toReal]
  ring

/-! ## Scale selection

For a vector with `|v[i]| ≤ 6 · 2^127` for all `i` (i.e., data fits
in the maximum representable range of MX), a non-NaN scale exists
such that all elements are in-range — `|v[i] / s| ≤ 6` after scaling.

The simplest existence proof picks `s = 2^127` (the maximum scale)
and the constraint `|v[i]| ≤ 6 · 2^127` reduces to the hypothesis.
A *minimal* (optimal) scale would pick `2^k` for
`k = ⌈log₂(max|v|/6)⌉` clamped to `[-127, 127]` — that requires
`Real.log` reasoning and is deferred. -/

/-- The maximum non-NaN E8M0 scale: `2^127`. -/
def maxScale : E8M0 := ⟨⟨254, by omega⟩⟩

@[simp] theorem maxScale_isNaN : maxScale.isNaN = false := by
  simp [E8M0.isNaN, maxScale, E8M0.nanRaw]

@[simp] theorem maxScale_toRealOrZero :
    maxScale.toRealOrZero = (2 : ℝ) ^ (127 : ℤ) := by
  unfold E8M0.toRealOrZero maxScale E8M0.bias E8M0.nanRaw
  simp

/-- **Existence of a fitting scale.**  Any vector whose absolute
    values are bounded by `6 · 2^127` admits a non-NaN E8M0 scale
    such that every element fits in the saturating range
    `[-6, 6] · s.toRealOrZero`.  Picking `s = maxScale` (a non-optimal
    but always-safe choice) satisfies this.  -/
theorem chooseScale_exists (v : List.Vector ℝ K)
    (hM : ∀ i, |v.get i| ≤ 6 * (2 : ℝ) ^ (127 : ℤ)) :
    ∃ s : E8M0, s.isNaN = false ∧
      ∀ i, |v.get i| ≤ 6 * s.toRealOrZero := by
  refine ⟨maxScale, maxScale_isNaN, ?_⟩
  intro i
  rw [maxScale_toRealOrZero]
  exact hM i

/-- **Optimal scale exists.**  Among all non-NaN scales that fit the
    data, there's one with minimum `toRealOrZero`.  Existence is via
    `Finset.exists_min_image` over the 256 E8M0 patterns filtered by
    the validity predicate — non-empty by `chooseScale_exists`.

    The optimal scale gives the tightest possible block-level error
    bound `|d - v[i]| ≤ s.toRealOrZero`, since smaller `s` ⇒ smaller
    bound. -/
theorem optimalScale_exists (v : List.Vector ℝ K)
    (hM : ∀ i, |v.get i| ≤ 6 * (2 : ℝ) ^ (127 : ℤ)) :
    ∃ s : E8M0, s.isNaN = false ∧
      (∀ i, |v.get i| ≤ 6 * s.toRealOrZero) ∧
      (∀ s' : E8M0, s'.isNaN = false →
        (∀ i, |v.get i| ≤ 6 * s'.toRealOrZero) →
        s.toRealOrZero ≤ s'.toRealOrZero) := by
  classical
  let valid : Finset E8M0 := (Finset.univ : Finset E8M0).filter
    (fun s => s.isNaN = false ∧ ∀ i, |v.get i| ≤ 6 * s.toRealOrZero)
  have hne : valid.Nonempty := by
    refine ⟨maxScale, ?_⟩
    simp only [valid, Finset.mem_filter, Finset.mem_univ, true_and, maxScale_isNaN]
    intro i
    rw [maxScale_toRealOrZero]
    exact hM i
  obtain ⟨s, hs_mem, hs_min⟩ :=
    valid.exists_min_image (fun s => s.toRealOrZero) hne
  rw [Finset.mem_filter] at hs_mem
  refine ⟨s, hs_mem.2.1, hs_mem.2.2, ?_⟩
  intro s' hs'_nan hs'_valid
  apply hs_min
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ s', hs'_nan, hs'_valid⟩

/-- Constructive optimal scale (via `Classical.choose`).  Requires the
    data to fit in the maximum representable range. -/
noncomputable def optimalScale (v : List.Vector ℝ K)
    (hM : ∀ i, |v.get i| ≤ 6 * (2 : ℝ) ^ (127 : ℤ)) : E8M0 :=
  Classical.choose (optimalScale_exists v hM)

theorem optimalScale_isNaN (v : List.Vector ℝ K)
    (hM : ∀ i, |v.get i| ≤ 6 * (2 : ℝ) ^ (127 : ℤ)) :
    (optimalScale v hM).isNaN = false :=
  (Classical.choose_spec (optimalScale_exists v hM)).1

theorem optimalScale_fits (v : List.Vector ℝ K)
    (hM : ∀ i, |v.get i| ≤ 6 * (2 : ℝ) ^ (127 : ℤ)) :
    ∀ i, |v.get i| ≤ 6 * (optimalScale v hM).toRealOrZero :=
  (Classical.choose_spec (optimalScale_exists v hM)).2.1

theorem optimalScale_minimal (v : List.Vector ℝ K)
    (hM : ∀ i, |v.get i| ≤ 6 * (2 : ℝ) ^ (127 : ℤ))
    (s' : E8M0) (hs'_nan : s'.isNaN = false)
    (hs'_valid : ∀ i, |v.get i| ≤ 6 * s'.toRealOrZero) :
    (optimalScale v hM).toRealOrZero ≤ s'.toRealOrZero :=
  (Classical.choose_spec (optimalScale_exists v hM)).2.2 s' hs'_nan hs'_valid

/-! ## Tight bound on the optimal scale

For data whose maximum magnitude is at least `3 · 2^(-127)`, the
optimal scale is bounded by `max|v|/3`.  Otherwise (very tiny data
near the smallest representable scale), the bound degrades to the
floor `2^(-127)`. -/

/-- The maximum absolute value in a non-empty vector. -/
noncomputable def maxAbs {K : Nat} (v : List.Vector ℝ (K + 1)) : ℝ :=
  (Finset.univ : Finset (Fin (K + 1))).sup'
    (Finset.univ_nonempty) (fun i => |v.get i|)

theorem le_maxAbs {K : Nat} (v : List.Vector ℝ (K + 1)) (i : Fin (K + 1)) :
    |v.get i| ≤ maxAbs v := by
  unfold maxAbs
  exact Finset.le_sup' (fun j => |v.get j|) (Finset.mem_univ i)

theorem maxAbs_nonneg {K : Nat} (v : List.Vector ℝ (K + 1)) :
    0 ≤ maxAbs v :=
  le_trans (abs_nonneg _) (le_maxAbs v ⟨0, by omega⟩)

/-- The half of a non-zero E8M0 scale: `2^(k-1)` for `s = 2^k`.
    Requires `s.raw.val > 0` (i.e., `k > -127`) so the half stays in
    range. -/
def halfScale (s : E8M0) (h : 0 < s.raw.val) : E8M0 :=
  ⟨⟨s.raw.val - 1, by have := s.raw.isLt; omega⟩⟩

theorem halfScale_isNaN (s : E8M0) (h : 0 < s.raw.val) :
    (halfScale s h).isNaN = false := by
  unfold halfScale E8M0.isNaN E8M0.nanRaw
  have := s.raw.isLt
  simp [Fin.ext_iff]; omega

theorem halfScale_toRealOrZero (s : E8M0) (h : 0 < s.raw.val)
    (hs : s.isNaN = false) :
    (halfScale s h).toRealOrZero = s.toRealOrZero / 2 := by
  unfold halfScale E8M0.toRealOrZero E8M0.bias E8M0.nanRaw
  have h_ne : s.raw ≠ (255 : Fin 256) := by
    intro heq
    simp [E8M0.isNaN, E8M0.nanRaw, heq] at hs
  have h_half_ne : (⟨s.raw.val - 1, by have := s.raw.isLt; omega⟩ : Fin 256) ≠
      (255 : Fin 256) := by
    intro heq
    rw [Fin.ext_iff] at heq
    have := s.raw.isLt
    simp at heq
    omega
  rw [if_neg h_ne, if_neg h_half_ne]
  have h1 : ((⟨s.raw.val - 1, by have := s.raw.isLt; omega⟩ : Fin 256).val : ℤ) =
            (s.raw.val : ℤ) - 1 := by
    push_cast; omega
  rw [h1]
  rw [show ((s.raw.val : ℤ) - 1 - 127 : ℤ) = ((s.raw.val : ℤ) - 127) - 1 from by ring]
  rw [zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- **Tight optimal-scale bound.**  For data whose max-abs is at least
    `3 · 2^(-127)`, the optimal scale is no larger than `max|v|/3`.
    Combined with `optimalScale_fits` (which gives `max|v| ≤ 6 · s`),
    this sandwiches the optimal scale to within a factor of 2 of the
    real-valued optimum.

    The argument: optimalScale is the smallest valid scale.  If its
    raw exponent is `> 0` (i.e., it's not at the lower clamp), the
    "half-scale" is also a non-NaN E8M0; by minimality, the half is
    not valid, so `6 · (s/2) < max|v|`, i.e., `s < max|v|/3`. -/
theorem optimalScale_le_third_maxAbs {K : Nat}
    (v : List.Vector ℝ (K + 1))
    (hM : ∀ i, |v.get i| ≤ 6 * (2 : ℝ) ^ (127 : ℤ))
    (h_lo : 3 * (2 : ℝ) ^ (-127 : ℤ) ≤ maxAbs v) :
    (optimalScale v hM).toRealOrZero ≤ maxAbs v / 3 := by
  set s := optimalScale v hM
  have hs_nan : s.isNaN = false := optimalScale_isNaN v hM
  have hs_pos : 0 < s.toRealOrZero := toRealOrZero_pos s hs_nan
  by_cases hraw : 0 < s.raw.val
  · -- s.raw > 0: half-scale is a valid E8M0.  Show it's not data-fitting.
    set sh := halfScale s hraw
    have hsh_nan : sh.isNaN = false := halfScale_isNaN s hraw
    have hsh_eq : sh.toRealOrZero = s.toRealOrZero / 2 :=
      halfScale_toRealOrZero s hraw hs_nan
    -- If sh were valid, optimalScale_minimal would give s ≤ sh, but
    -- sh = s/2 < s — contradiction.  So sh is NOT data-fitting.
    have hsh_invalid : ¬ ∀ i, |v.get i| ≤ 6 * sh.toRealOrZero := by
      intro h_valid
      have := optimalScale_minimal v hM sh hsh_nan h_valid
      rw [hsh_eq] at this
      linarith
    -- ¬ ∀ i ⇒ ∃ i.  Get a violating index.
    push_neg at hsh_invalid
    obtain ⟨i, hi⟩ := hsh_invalid
    -- `|v[i]| > 6 · s/2 = 3 · s` and `|v[i]| ≤ maxAbs v`.
    rw [hsh_eq] at hi
    have hmax_lo : 3 * s.toRealOrZero < maxAbs v :=
      lt_of_lt_of_le (by linarith) (le_maxAbs v i)
    linarith
  · -- s.raw = 0, i.e., s = 2^(-127).  Use h_lo directly.
    push_neg at hraw
    have hraw_eq : s.raw.val = 0 := by omega
    have hs_eq : s.toRealOrZero = (2 : ℝ) ^ (-127 : ℤ) := by
      unfold E8M0.toRealOrZero E8M0.bias E8M0.nanRaw
      have h_ne : s.raw ≠ (255 : Fin 256) := by
        intro heq; simp [E8M0.isNaN, E8M0.nanRaw, heq] at hs_nan
      rw [if_neg h_ne]
      have : ((s.raw.val : ℤ) - 127 : ℤ) = -127 := by rw [hraw_eq]; ring
      rw [this]
    rw [hs_eq]
    -- h_lo: 3 * 2^(-127) ≤ maxAbs v.  Goal: 2^(-127) ≤ maxAbs v / 3.
    rw [le_div_iff₀ (by norm_num : (3 : ℝ) > 0)]
    linarith

/-- A scale-selection function.  Always returns a non-NaN scale.
    For data with `|v[i]| ≤ 6 · 2^127`, the returned scale guarantees
    no element saturates after scaling. -/
noncomputable def chooseScale (_v : List.Vector ℝ K) : E8M0 :=
  -- Currently a non-optimal max-scale fallback.  An optimal selection
  -- would solve `2^k = ⌈max|v|/6⌉` with clamping; deferred.
  maxScale

@[simp] theorem chooseScale_isNaN (v : List.Vector ℝ K) :
    (chooseScale v).isNaN = false := maxScale_isNaN

@[simp] theorem chooseScale_toRealOrZero (v : List.Vector ℝ K) :
    (chooseScale v).toRealOrZero = (2 : ℝ) ^ (127 : ℤ) := maxScale_toRealOrZero

/-- The fitting property of `chooseScale` for bounded data. -/
theorem chooseScale_fits (v : List.Vector ℝ K)
    (hM : ∀ i, |v.get i| ≤ 6 * (2 : ℝ) ^ (127 : ℤ)) :
    ∀ i, |v.get i| ≤ 6 * (chooseScale v).toRealOrZero := by
  intro i
  rw [chooseScale_toRealOrZero]
  exact hM i

/-- Top-level encoder: pick a scale and round each element. -/
noncomputable def encode (v : List.Vector ℝ K) : MXBlock K :=
  encodeWithScale v (chooseScale v)

@[simp] theorem encode_scale (v : List.Vector ℝ K) :
    (encode v).scale = chooseScale v := rfl

/-! ## Block-level error bound

For each element with `|v[i]| ≤ 6 · s.toRealOrZero` (so the scaled
value `v[i]/s` is in `[-6, 6] ⊂ (-7, 7)` and never saturates), the
decoded value is within `s.toRealOrZero` of `v[i]`. -/

/-- **Per-element error bound.**  For data fitting the saturating
    range with respect to `s`, the decoded element is within
    `s.toRealOrZero` of the original.  Combines the RNE error bound
    `|roundRNE(x) - x| ≤ 1` with the scale factor. -/
theorem encodeWithScale_decodeAt_error
    (v : List.Vector ℝ K) (s : E8M0) (i : Fin K)
    (hns : s.isNaN = false)
    (hM : |v.get i| ≤ 6 * s.toRealOrZero) :
    ∃ d : ℝ, (encodeWithScale v s).decodeAt i = some d ∧
      |d - v.get i| ≤ s.toRealOrZero := by
  have hsv_pos : 0 < s.toRealOrZero := toRealOrZero_pos s hns
  have h_in : |v.get i / s.toRealOrZero| < E2M1.overflowBoundary := by
    rw [abs_div, abs_of_pos hsv_pos]
    rw [E2M1.overflowBoundary]
    rw [div_lt_iff₀ hsv_pos]
    calc |v.get i| ≤ 6 * s.toRealOrZero := hM
      _ < 7 * s.toRealOrZero := by nlinarith
  have h_err : |(roundRNE (v.get i / s.toRealOrZero)).toReal - v.get i / s.toRealOrZero| ≤ 1 :=
    E2M1.roundRNE_error_bound _ h_in
  refine ⟨_, decodeAt_encodeWithScale v s i hns, ?_⟩
  -- Goal: |s * roundRNE(v[i]/s) - v[i]| ≤ s
  set q := v.get i / s.toRealOrZero with hq_def
  set z := (roundRNE q).toReal with hz_def
  have hvi : v.get i = s.toRealOrZero * q := by
    rw [hq_def]; field_simp
  rw [hvi]
  have : s.toRealOrZero * z - s.toRealOrZero * q = s.toRealOrZero * (z - q) := by ring
  rw [this, abs_mul, abs_of_pos hsv_pos]
  calc s.toRealOrZero * |z - q| ≤ s.toRealOrZero * 1 := by
        apply mul_le_mul_of_nonneg_left h_err hsv_pos.le
    _ = s.toRealOrZero := by ring

/-- **Block-level error bound.**  For an in-range vector, every decoded
    element is within `chooseScale v . toRealOrZero` of the original. -/
theorem encode_decodeAt_error
    (v : List.Vector ℝ K) (i : Fin K)
    (hM : ∀ i, |v.get i| ≤ 6 * (2 : ℝ) ^ (127 : ℤ)) :
    ∃ d : ℝ, (encode v).decodeAt i = some d ∧
      |d - v.get i| ≤ (chooseScale v).toRealOrZero := by
  unfold encode
  apply encodeWithScale_decodeAt_error _ _ _ (chooseScale_isNaN v)
  rw [chooseScale_toRealOrZero]
  exact hM i

/-! ## Top-level encoder with optimal scale

`encodeOptimal` selects the smallest valid E8M0 scale, giving the
tightest per-element error bound `|d - v[i]| ≤ optimalScale.toRealOrZero`.
The optimality is *over* the 256 E8M0 patterns, not the conceptual
real-valued optimum, so the bound is at most a factor of 2 looser
than `max|v|/3`. -/

/-- Top-level optimal encoder.  Requires bounded data
    (`max |v[i]| ≤ 6 · 2^127`) so the optimal scale is well-defined. -/
noncomputable def encodeOptimal (v : List.Vector ℝ K)
    (hM : ∀ i, |v.get i| ≤ 6 * (2 : ℝ) ^ (127 : ℤ)) : MXBlock K :=
  encodeWithScale v (optimalScale v hM)

/-- The encoder uses the optimal scale. -/
@[simp] theorem encodeOptimal_scale (v : List.Vector ℝ K)
    (hM : ∀ i, |v.get i| ≤ 6 * (2 : ℝ) ^ (127 : ℤ)) :
    (encodeOptimal v hM).scale = optimalScale v hM := rfl

/-- **Optimal block-level error bound.**  Tighter than
    `encode_decodeAt_error` when the data magnitude is much less than
    `2^127`: the bound is the optimal scale, not `2^127`. -/
theorem encodeOptimal_decodeAt_error
    (v : List.Vector ℝ K) (i : Fin K)
    (hM : ∀ i, |v.get i| ≤ 6 * (2 : ℝ) ^ (127 : ℤ)) :
    ∃ d : ℝ, (encodeOptimal v hM).decodeAt i = some d ∧
      |d - v.get i| ≤ (optimalScale v hM).toRealOrZero := by
  unfold encodeOptimal
  apply encodeWithScale_decodeAt_error _ _ _ (optimalScale_isNaN v hM)
  exact optimalScale_fits v hM i

/-- The optimal-encoder error bound is at most that of the maxScale-based
    encoder.  Combines `encodeOptimal_decodeAt_error` with
    `optimalScale_minimal`. -/
theorem encodeOptimal_decodeAt_error_le_chooseScale
    (v : List.Vector ℝ K) (i : Fin K)
    (hM : ∀ i, |v.get i| ≤ 6 * (2 : ℝ) ^ (127 : ℤ)) :
    (optimalScale v hM).toRealOrZero ≤ (chooseScale v).toRealOrZero := by
  rw [chooseScale_toRealOrZero]
  have hmax : maxScale.toRealOrZero = (2 : ℝ) ^ (127 : ℤ) :=
    maxScale_toRealOrZero
  rw [← hmax]
  exact optimalScale_minimal v hM maxScale maxScale_isNaN
    (fun i => by rw [maxScale_toRealOrZero]; exact hM i)

end MXBlock
end MX
