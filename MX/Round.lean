import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MX.E2M1

/-! # Rounding modes for E2M1

E2M1 has 16 representable values forming the set
`{0, ±0.5, ±1, ±1.5, ±2, ±3, ±4, ±6}`.  Rounding from `ℝ` to `E2M1`
selects one of these 16 values according to a rounding mode.

Differences from IEEE 754 rounding:

  *  **No infinity.**  Out-of-range values *saturate* to `±6`, not
     to `±∞` — there is no `±∞` to round to.
  *  **Smaller representable set.**  The interesting rounding cases
     are sparse: between `+4` and `+6` is a wide gap with no
     intermediate representable, so most of `[4, 6]` rounds to `4`
     and most of `[6, 8]` saturates to `6`.

This module defines:

  *  `RoundingMode` — the IEEE 754 §4.3 modes plus stochastic.
  *  `IsRoundedTo* r z` — per-mode predicates for `r : ℝ`, `z : E2M1`.
  *  Saturation theorems pinning the overflow rule.

Existence of constructive `roundTo*` functions is straightforward
(brute-force over the 16 values) but deferred — adding them follows
the same `Finset.exists_min_image` template as `IEEEFloat`.
-/

namespace MX
namespace E2M1

/-- The maximum representable magnitude.  Closed-form: `6`. -/
def maxAbs : ℝ := 6

/-- The "overflow boundary" for round-to-nearest.  Magnitudes
    strictly less than this round to a finite (≤ `maxAbs`) E2M1;
    magnitudes at or beyond saturate to `±maxAbs`.

    Value: `maxAbs + topUlp/2 = 6 + 1 = 7`, where `topUlp = 2`
    is the gap between `+4` and `+6` (the gap at the top of the
    representable range). -/
def overflowBoundary : ℝ := 7

/-! ## Rounding modes -/

/-- The five IEEE 754-2019 directed rounding modes plus stochastic
    rounding (used in QAT). -/
inductive RoundingMode
  | tiesToEven
  | tiesToAway
  | towardZero
  | towardPositive
  | towardNegative
  | stochastic
  deriving DecidableEq, Repr

/-! ## Round-to-nearest-even predicate

The default rounding mode.  Saturates at `overflowBoundary`. -/

/-- `IsRoundedToNearestEven r z`: `z : E2M1` is a round-to-nearest-even
    encoding of `r : ℝ`.  Saturates to `±6` on overflow. -/
def IsRoundedToNearestEven (r : ℝ) (z : E2M1) : Prop :=
  -- Overflow: saturate to ±6 (not to ±∞ — no infinity in MXFP4).
  (overflowBoundary ≤ |r| →
      (0 ≤ r → z = ⟨false, 3, 1⟩) ∧ (r < 0 → z = ⟨true, 3, 1⟩)) ∧
  -- In-range: nearest E2M1, ties to even.
  (|r| < overflowBoundary →
      (∀ y : E2M1, |z.toReal - r| ≤ |y.toReal - r|) ∧
      (∀ y : E2M1, y ≠ z →
        |z.toReal - r| = |y.toReal - r| → z.m.val % 2 = 0))

/-! ## Round-toward-zero predicate (truncation) -/

/-- `IsRoundedTowardZero r z`: `z`'s magnitude does not exceed `|r|`,
    and `z` is the closest such value.  Saturates to `±6` on overflow
    (since `|±6| = 6` is the largest finite). -/
def IsRoundedTowardZero (r : ℝ) (z : E2M1) : Prop :=
  -- Positive overflow: z = +6
  (overflowBoundary ≤ r → z = ⟨false, 3, 1⟩) ∧
  -- Negative overflow: z = -6
  (r ≤ -overflowBoundary → z = ⟨true, 3, 1⟩) ∧
  -- In-range: nearest with |z| ≤ |r|
  (|r| < overflowBoundary →
      |z.toReal| ≤ |r| ∧
      (∀ y : E2M1, |y.toReal| ≤ |r| → |y.toReal| ≤ |z.toReal|))

/-! ## Stochastic rounding predicate

Stochastic rounding (SR) is used in QAT (quantization-aware training)
to provide *unbiased* gradient estimates.  Given `r` between two
adjacent representables `a ≤ r ≤ b`:

  *  result = `a` with probability `(b - r) / (b - a)`
  *  result = `b` with probability `(r - a) / (b - a)`

so `E[result] = a · (b - r)/(b - a) + b · (r - a)/(b - a) = r`,
unbiased.

The deterministic spec captures the *support* of the distribution:
the result is one of the two adjacent representables straddling `r`.
The probabilistic / expectation properties are stated separately
(below). -/

/-- `IsValidStochasticRound r z`: `z` is a candidate result of
    stochastic rounding `r`.  Either:

    *  `r` is out of range and `z` is the saturating `±6`, or
    *  `z` is one of the two grid-adjacent representables to `r`,
       i.e., either `z ≤ r` with no representable strictly in `(z, r]`
       (lower-adjacent), or `r ≤ z` with no representable strictly in
       `[r, z)` (upper-adjacent).

    The probability semantics (which of the two `z` is chosen) is
    captured by `stochasticRoundProb` separately. -/
def IsValidStochasticRound (r : ℝ) (z : E2M1) : Prop :=
  -- Saturating cases: same as RTZ for out-of-range.
  (overflowBoundary ≤ r → z = ⟨false, 3, 1⟩) ∧
  (r ≤ -overflowBoundary → z = ⟨true, 3, 1⟩) ∧
  -- In-range: z is grid-adjacent to r (lower or upper).
  (|r| < overflowBoundary →
    (z.toReal ≤ r ∧ ∀ y : E2M1, z.toReal < y.toReal → r < y.toReal) ∨
    (r ≤ z.toReal ∧ ∀ y : E2M1, y.toReal < z.toReal → y.toReal < r))

/-- The probability that stochastic rounding produces `z`, given the
    real value `r`.  Defined as `(r - lower) / (upper - lower)` where
    `lower, upper` are the two adjacent E2M1 values straddling `r`,
    and `z` is whichever side. -/
noncomputable def stochasticRoundProb
    (r : ℝ) (lower upper z : E2M1) : ℝ :=
  if z = upper then
    (r - lower.toReal) / (upper.toReal - lower.toReal)
  else if z = lower then
    (upper.toReal - r) / (upper.toReal - lower.toReal)
  else 0

/-- The two probabilities for adjacent E2M1 values sum to 1. -/
theorem stochasticRoundProb_sum_one
    (r : ℝ) (lower upper : E2M1)
    (h_lt : lower.toReal < upper.toReal) (h_ne : lower ≠ upper) :
    stochasticRoundProb r lower upper upper +
    stochasticRoundProb r lower upper lower = 1 := by
  unfold stochasticRoundProb
  rw [if_pos rfl, if_neg h_ne, if_pos rfl]
  have h_diff_ne : upper.toReal - lower.toReal ≠ 0 := by linarith
  rw [← add_div]
  rw [show (r - lower.toReal + (upper.toReal - r) : ℝ) = upper.toReal - lower.toReal from by ring]
  exact div_self h_diff_ne

/-- Stochastic rounding is **unbiased**: the probability-weighted
    average of the two adjacent representables equals `r` exactly. -/
theorem stochasticRound_unbiased
    (r : ℝ) (lower upper : E2M1)
    (h_lt : lower.toReal < upper.toReal) (h_ne : lower ≠ upper) :
    stochasticRoundProb r lower upper upper * upper.toReal +
    stochasticRoundProb r lower upper lower * lower.toReal
      = r := by
  unfold stochasticRoundProb
  rw [if_pos rfl, if_neg h_ne, if_pos rfl]
  have h_diff_ne : upper.toReal - lower.toReal ≠ 0 := by linarith
  field_simp
  ring

/-! ## Existence of stochastic rounding

For any `r`, some `E2M1` value satisfies `IsValidStochasticRound`.
Saturation pins the boundary cases; in-range, the lower-adjacent
witness exists via `Finset.exists_max_image` over the finite type
`E2M1` filtered by `y.toReal ≤ r` (non-empty because `-6 ≤ r` when
`|r| < 7`). -/

private theorem _overflowBoundary_pos_local : (0 : ℝ) < overflowBoundary := by
  unfold overflowBoundary; norm_num

theorem sr_exists (r : ℝ) : ∃ z : E2M1, IsValidStochasticRound r z := by
  classical
  have hOB := _overflowBoundary_pos_local
  by_cases hover_pos : overflowBoundary ≤ r
  · refine ⟨⟨false, 3, 1⟩, fun _ => rfl, ?_, ?_⟩
    · intro h; exfalso; linarith
    · intro h; exfalso
      have habs : |r| = r := abs_of_nonneg (le_trans hOB.le hover_pos)
      rw [habs] at h; linarith
  by_cases hover_neg : r ≤ -overflowBoundary
  · refine ⟨⟨true, 3, 1⟩, ?_, fun _ => rfl, ?_⟩
    · intro h; exfalso; linarith
    · intro h; exfalso
      have hle : r ≤ 0 := by linarith
      have habs : |r| = -r := abs_of_nonpos hle
      rw [habs] at h; linarith
  · push_neg at hover_pos hover_neg
    -- In-range: r ∈ (-7, 7).  Upper-adjacent always exists since +6 ≥ r
    -- when r ≤ 6, and lower-adjacent always exists when r ≥ -6.  We
    -- branch on whether `r ≥ -6` so the lower-adjacent witness ⟨true, 3, 1⟩
    -- (= -6) sits in the filtered set.
    by_cases h6 : -6 ≤ r
    · -- Lower-adjacent.
      let lowerSet : Finset E2M1 :=
        (Finset.univ : Finset E2M1).filter (fun y => y.toReal ≤ r)
      have hne : lowerSet.Nonempty := by
        refine ⟨⟨true, 3, 1⟩, ?_⟩
        simp only [lowerSet, Finset.mem_filter, Finset.mem_univ, true_and,
          toReal_neg_six]
        exact h6
      obtain ⟨z, hz_mem, hz_max⟩ :=
        lowerSet.exists_max_image (fun y => y.toReal) hne
      have hz_le : z.toReal ≤ r := (Finset.mem_filter.mp hz_mem).2
      refine ⟨z, ?_, ?_, ?_⟩
      · intro h; exfalso; linarith
      · intro h; exfalso; linarith
      · intro _
        left
        refine ⟨hz_le, ?_⟩
        intro y hy_gt
        by_contra h
        push_neg at h
        have hy_in : y ∈ lowerSet := by
          rw [Finset.mem_filter]; exact ⟨Finset.mem_univ y, h⟩
        have := hz_max y hy_in
        linarith
    · -- r < -6.  Use upper-adjacent z = -6.
      push_neg at h6
      refine ⟨⟨true, 3, 1⟩, ?_, ?_, ?_⟩
      · intro h; exfalso; linarith
      · intro h; exfalso; linarith
      · intro _
        right
        rw [toReal_neg_six]
        refine ⟨by linarith, ?_⟩
        intro y hy_lt
        -- y.toReal < -6, but every E2M1 has toReal ≥ -6, contradiction.
        exfalso
        have hy_ge : -6 ≤ y.toReal := by
          obtain ⟨ys, ye, ⟨ym_val, hym_lt⟩⟩ := y
          have hm : ym_val = 0 ∨ ym_val = 1 := by omega
          rcases ys with _ | _ <;> fin_cases ye <;>
            rcases hm with rfl | rfl <;>
              (dsimp [toReal, bias]; norm_num)
        linarith

/-- Constructive stochastic round.  Picks the lower-adjacent
    representative when in-range; saturating value on overflow.  This
    is one of the (up to) two valid candidates — combine with
    `stochasticRoundProb` and the unbiasedness theorem to model the
    full stochastic distribution. -/
noncomputable def roundSR (r : ℝ) : E2M1 :=
  Classical.choose (sr_exists r)

theorem roundSR_isValidSR (r : ℝ) :
    IsValidStochasticRound r (roundSR r) :=
  Classical.choose_spec (sr_exists r)

/-! ## Subnormal flush helper

The FTZ (flush-to-zero) variant of any rounding mode replaces the
subnormal output pattern `(s, 0, 1)` (i.e., `±0.5` in E2M1) with
`(s, 0, 0)` (i.e., `±0`).  Defined here so it's available before
`roundRNE_FTZ` below. -/

/-- True iff the value is the subnormal pattern (`±0.5`). -/
def isSubnormalPattern (z : E2M1) : Bool :=
  z.e.val = 0 ∧ z.m.val = 1

/-- Replace `(s, 0, 1) ↦ (s, 0, 0)` (i.e., `±0.5 ↦ ±0`); leave
    everything else alone. -/
def flushSubnormal (z : E2M1) : E2M1 :=
  if z.e.val = 0 ∧ z.m.val = 1 then ⟨z.s, 0, 0⟩ else z

@[simp] theorem flushSubnormal_subnormal (s : Bool) :
    flushSubnormal ⟨s, 0, 1⟩ = ⟨s, 0, 0⟩ := by
  unfold flushSubnormal; simp

theorem flushSubnormal_not_subnormal (z : E2M1)
    (h : ¬ (z.e.val = 0 ∧ z.m.val = 1)) :
    flushSubnormal z = z := by
  unfold flushSubnormal; rw [if_neg h]

/-- The flushed value's real interpretation: `±0` for the subnormal
    case, otherwise unchanged. -/
theorem flushSubnormal_toReal (z : E2M1) :
    (flushSubnormal z).toReal =
      (if z.e.val = 0 ∧ z.m.val = 1 then 0 else z.toReal) := by
  unfold flushSubnormal
  split_ifs with h
  · rcases h_s : z.s with _ | _
    · show toReal ⟨false, 0, 0⟩ = 0; rw [toReal_pos_zero]
    · show toReal ⟨true, 0, 0⟩ = 0; rw [toReal_neg_zero]
  · rfl

/-! ## Saturation theorems

Pin down the saturation behavior so it can be cited directly from
downstream proofs. -/

theorem rne_saturates_pos (r : ℝ) (h : overflowBoundary ≤ r) :
    ∀ z : E2M1, IsRoundedToNearestEven r z → z = ⟨false, 3, 1⟩ := by
  intro z hz
  have h_abs : overflowBoundary ≤ |r| := by
    have h_pos : 0 ≤ r := by
      have : (0 : ℝ) < overflowBoundary := by unfold overflowBoundary; norm_num
      linarith
    rw [abs_of_nonneg h_pos]
    exact h
  have h_pos_r : 0 ≤ r := by
    have : (0 : ℝ) < overflowBoundary := by unfold overflowBoundary; norm_num
    linarith
  exact (hz.1 h_abs).1 h_pos_r

theorem rne_saturates_neg (r : ℝ) (h : r ≤ -overflowBoundary) :
    ∀ z : E2M1, IsRoundedToNearestEven r z → z = ⟨true, 3, 1⟩ := by
  intro z hz
  have h_neg_r : r < 0 := by
    have : (0 : ℝ) < overflowBoundary := by unfold overflowBoundary; norm_num
    linarith
  have h_abs : overflowBoundary ≤ |r| := by
    rw [abs_of_neg h_neg_r]
    linarith
  exact (hz.1 h_abs).2 h_neg_r

/-! ## Existence of round-toward-zero

`IsRoundedTowardZero` is satisfied for every `r : ℝ` — the saturating
boundary cases are pinned by definition, and the in-range case is
`Finset.exists_max_image` over the finite type `E2M1` filtered by
`|y.toReal| ≤ |r|` (which is non-empty: `+0` qualifies). -/

private theorem overflowBoundary_pos : (0 : ℝ) < overflowBoundary := by
  unfold overflowBoundary; norm_num

theorem rtz_exists (r : ℝ) : ∃ z : E2M1, IsRoundedTowardZero r z := by
  by_cases hpos_over : overflowBoundary ≤ r
  · -- Positive overflow: z = +6
    refine ⟨⟨false, 3, 1⟩, fun _ => rfl, ?_, ?_⟩
    · intro h
      exfalso
      have := overflowBoundary_pos
      linarith
    · intro h
      exfalso
      have hge0 : 0 ≤ r := le_trans overflowBoundary_pos.le hpos_over
      rw [abs_of_nonneg hge0] at h
      linarith
  by_cases hneg_over : r ≤ -overflowBoundary
  · -- Negative overflow: z = -6
    refine ⟨⟨true, 3, 1⟩, ?_, fun _ => rfl, ?_⟩
    · intro h; exfalso; linarith
    · intro h
      exfalso
      have hle0 : r ≤ 0 := by
        have := overflowBoundary_pos
        linarith
      rw [abs_of_nonpos hle0] at h
      linarith
  · -- In-range: pick the magnitude-largest E2M1 with |y.toReal| ≤ |r|.
    push_neg at hpos_over hneg_over
    have habs : |r| < overflowBoundary :=
      abs_lt.mpr ⟨by linarith, hpos_over⟩
    let S : Finset E2M1 :=
      (Finset.univ : Finset E2M1).filter (fun y => |y.toReal| ≤ |r|)
    have hS_nonempty : S.Nonempty := by
      refine ⟨⟨false, 0, 0⟩, ?_⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [toReal_pos_zero]
      simp [abs_nonneg]
    obtain ⟨z, hz_mem, hz_max⟩ :=
      S.exists_max_image (fun y => |y.toReal|) hS_nonempty
    refine ⟨z, ?_, ?_, ?_⟩
    · intro h; exfalso; linarith
    · intro h; exfalso; linarith
    · intro _
      have hz_filt : |z.toReal| ≤ |r| := (Finset.mem_filter.mp hz_mem).2
      refine ⟨hz_filt, ?_⟩
      intro y hy
      apply hz_max
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hy

/-- Constructive round-toward-zero (truncation).  Picks the
    saturating value on overflow, otherwise the magnitude-largest
    representable not exceeding `|r|`. -/
noncomputable def roundTowardZero (r : ℝ) : E2M1 :=
  Classical.choose (rtz_exists r)

theorem roundTowardZero_isRTZ (r : ℝ) :
    IsRoundedTowardZero r (roundTowardZero r) :=
  Classical.choose_spec (rtz_exists r)

/-! ## Existence of round-to-nearest-even

The RNE existence proof has two ingredients:

  *  A min-distance witness via `Finset.exists_min_image`.
  *  A tie-break helper: among any two distinct E2M1 values that both
     achieve the same distance to `r`, there is an even-mantissa E2M1
     at distance `≤` to that distance.  This is established by
     brute-force casework over the 28 ordered pairs of distinct odd
     values (since the case where one of `x, y` is even is trivial).

Together they show the predicate is satisfied: pick the closest even
when the global min has a tie partner, else the global min itself
(which has no tie, so the even-clause is vacuous). -/

/-- For any pair of E2M1 values with `a.toReal < b.toReal`, both with
    odd mantissa, there exists an even-mantissa E2M1 within `(b - a)/2`
    of the midpoint `(a.toReal + b.toReal)/2`.  Brute-force over the
    28 such ordered pairs.

    This is the key structural fact for RNE tie-breaking: when two
    values tie for nearest, they straddle `r` at midpoint, and an even
    value is at least as close. -/
private theorem odd_pair_midpoint_has_close_even
    (a b : E2M1) (ha : a.m.val = 1) (hb : b.m.val = 1)
    (h_lt : a.toReal < b.toReal) :
    ∃ z : E2M1, z.m.val = 0 ∧
      |z.toReal - (a.toReal + b.toReal) / 2| ≤ (b.toReal - a.toReal) / 2 := by
  obtain ⟨as, ae, ⟨am_val, ham_lt⟩⟩ := a
  obtain ⟨bs, be, ⟨bm_val, hbm_lt⟩⟩ := b
  simp only at ha hb
  subst ha; subst hb
  rcases as with _ | _ <;> rcases bs with _ | _ <;>
    fin_cases ae <;> fin_cases be <;>
      (first
        | (exfalso; dsimp [toReal, bias] at h_lt; linarith)
        | (refine ⟨⟨false, 0, 0⟩, rfl, ?_⟩
           show |((⟨false, 0, 0⟩ : E2M1)).toReal - _| ≤ _
           dsimp [toReal, bias]; norm_num; done)
        | (refine ⟨⟨false, 1, 0⟩, rfl, ?_⟩
           show |((⟨false, 1, 0⟩ : E2M1)).toReal - _| ≤ _
           dsimp [toReal, bias]; norm_num; done)
        | (refine ⟨⟨false, 2, 0⟩, rfl, ?_⟩
           show |((⟨false, 2, 0⟩ : E2M1)).toReal - _| ≤ _
           dsimp [toReal, bias]; norm_num; done)
        | (refine ⟨⟨false, 3, 0⟩, rfl, ?_⟩
           show |((⟨false, 3, 0⟩ : E2M1)).toReal - _| ≤ _
           dsimp [toReal, bias]; norm_num; done)
        | (refine ⟨⟨true, 0, 0⟩, rfl, ?_⟩
           show |((⟨true, 0, 0⟩ : E2M1)).toReal - _| ≤ _
           dsimp [toReal, bias]; norm_num; done)
        | (refine ⟨⟨true, 1, 0⟩, rfl, ?_⟩
           show |((⟨true, 1, 0⟩ : E2M1)).toReal - _| ≤ _
           dsimp [toReal, bias]; norm_num; done)
        | (refine ⟨⟨true, 2, 0⟩, rfl, ?_⟩
           show |((⟨true, 2, 0⟩ : E2M1)).toReal - _| ≤ _
           dsimp [toReal, bias]; norm_num; done)
        | (refine ⟨⟨true, 3, 0⟩, rfl, ?_⟩
           show |((⟨true, 3, 0⟩ : E2M1)).toReal - _| ≤ _
           dsimp [toReal, bias]; norm_num))

/-- Equidistance + ordering ⇒ `r` is the midpoint and the distance
    equals half the gap. -/
private lemma tie_implies_midpoint
    (a b r : ℝ) (h_lt : a < b) (h_dist : |a - r| = |b - r|) :
    r = (a + b) / 2 ∧ |a - r| = (b - a) / 2 := by
  have ha_le : a ≤ r := by
    by_contra h
    push_neg at h
    have h1 : 0 < a - r := by linarith
    have h2 : 0 < b - r := by linarith
    rw [abs_of_pos h1, abs_of_pos h2] at h_dist
    linarith
  have hb_ge : r ≤ b := by
    by_contra h
    push_neg at h
    have h1 : a - r < 0 := by linarith
    have h2 : b - r < 0 := by linarith
    rw [abs_of_neg h1, abs_of_neg h2] at h_dist
    linarith
  have h1 : a - r ≤ 0 := by linarith
  have h2 : 0 ≤ b - r := by linarith
  rw [abs_of_nonpos h1, abs_of_nonneg h2] at h_dist
  have h3 : r = (a + b) / 2 := by linarith
  refine ⟨h3, ?_⟩
  rw [h3, abs_of_nonpos]
  · linarith
  · linarith

/-- Distinct odd-mantissa E2M1 values have distinct `toReal`s.
    Proved by brute-force casework over the 8 odd values. -/
private lemma odd_toReal_inj
    (x y : E2M1) (hx : x.m.val = 1) (hy : y.m.val = 1)
    (h_eq : x.toReal = y.toReal) : x = y := by
  obtain ⟨xs, xe, ⟨xm_val, hxm_lt⟩⟩ := x
  obtain ⟨ys, ye, ⟨ym_val, hym_lt⟩⟩ := y
  simp only at hx hy
  subst hx; subst hy
  rcases xs with _ | _ <;> rcases ys with _ | _ <;>
    fin_cases xe <;> fin_cases ye <;>
      first
      | rfl
      | (exfalso; revert h_eq; dsimp [toReal, bias]; norm_num)

/-- For any `r` and tied pair `(x, y)` with `x ≠ y`, there is an
    even-mantissa E2M1 at distance ≤ to `|x.toReal - r|`. -/
private lemma tie_even_witness
    (r : ℝ) (x y : E2M1) (hxy : x ≠ y)
    (h_dist : |x.toReal - r| = |y.toReal - r|) :
    ∃ z : E2M1, z.m.val = 0 ∧ |z.toReal - r| ≤ |x.toReal - r| := by
  by_cases hx_even : x.m.val = 0
  · exact ⟨x, hx_even, le_refl _⟩
  by_cases hy_even : y.m.val = 0
  · exact ⟨y, hy_even, by rw [← h_dist]⟩
  have hx_odd : x.m.val = 1 := by have := x.m.isLt; omega
  have hy_odd : y.m.val = 1 := by have := y.m.isLt; omega
  -- Both odd ⇒ x.toReal ≠ y.toReal (by injectivity).
  have h_ne : x.toReal ≠ y.toReal := fun h_eq =>
    hxy (odd_toReal_inj x y hx_odd hy_odd h_eq)
  rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
  · obtain ⟨z, hz_even, hz_dist⟩ :=
      odd_pair_midpoint_has_close_even x y hx_odd hy_odd h_lt
    obtain ⟨hmid, hxd⟩ := tie_implies_midpoint x.toReal y.toReal r h_lt h_dist
    refine ⟨z, hz_even, ?_⟩
    rw [← hmid] at hz_dist; rw [hxd]; exact hz_dist
  · obtain ⟨z, hz_even, hz_dist⟩ :=
      odd_pair_midpoint_has_close_even y x hy_odd hx_odd h_gt
    obtain ⟨hmid, hyd⟩ := tie_implies_midpoint y.toReal x.toReal r h_gt h_dist.symm
    refine ⟨z, hz_even, ?_⟩
    rw [← hmid] at hz_dist
    rw [h_dist, hyd]
    exact hz_dist

/-- **Existence of round-to-nearest-even.**  For every `r : ℝ`, some
    `E2M1` value satisfies the RNE predicate.  Saturates to `±6` on
    overflow; otherwise picks an even-mantissa minimizer when one
    achieves the global minimum distance, else the unique odd
    minimizer (which has no tie partner). -/
theorem rne_exists (r : ℝ) : ∃ z : E2M1, IsRoundedToNearestEven r z := by
  by_cases hover : overflowBoundary ≤ |r|
  · by_cases hpos : 0 ≤ r
    · refine ⟨⟨false, 3, 1⟩, ?_, ?_⟩
      · intro _
        refine ⟨fun _ => rfl, fun hr => ?_⟩
        exfalso; linarith
      · intro h; exfalso; linarith
    · push_neg at hpos
      refine ⟨⟨true, 3, 1⟩, ?_, ?_⟩
      · intro _
        refine ⟨fun hr => ?_, fun _ => rfl⟩
        exfalso; linarith
      · intro h; exfalso; linarith
  · push_neg at hover
    obtain ⟨x, _, hx_min⟩ :=
      (Finset.univ : Finset E2M1).exists_min_image
        (fun y => |y.toReal - r|) Finset.univ_nonempty
    let evenSet : Finset E2M1 :=
      (Finset.univ : Finset E2M1).filter
        (fun y => y.m.val = 0 ∧ |y.toReal - r| ≤ |x.toReal - r|)
    by_cases h_even : evenSet.Nonempty
    · obtain ⟨z, hz_mem⟩ := h_even
      have hz := Finset.mem_filter.mp hz_mem
      have hz_even : z.m.val = 0 := hz.2.1
      have hz_le : |z.toReal - r| ≤ |x.toReal - r| := hz.2.2
      have hz_dist : |z.toReal - r| = |x.toReal - r| :=
        le_antisymm hz_le (hx_min z (Finset.mem_univ z))
      refine ⟨z, fun hcontra => absurd hcontra (not_le.mpr hover), fun _ => ?_⟩
      refine ⟨?_, ?_⟩
      · intro y; rw [hz_dist]; exact hx_min y (Finset.mem_univ y)
      · intro _ _ _; omega
    · refine ⟨x, fun hcontra => absurd hcontra (not_le.mpr hover), fun _ => ?_⟩
      refine ⟨fun y => hx_min y (Finset.mem_univ y), ?_⟩
      intro y hy_ne hy_dist
      -- Tie partner exists ⇒ even at min distance ⇒ evenSet non-empty.
      exfalso
      apply h_even
      obtain ⟨z, hz_even, hz_le⟩ := tie_even_witness r x y hy_ne.symm hy_dist
      refine ⟨z, ?_⟩
      simp only [evenSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hz_even, hz_le⟩

/-- Constructive round-to-nearest-even.  Picks an even-mantissa
    minimizer when ties exist, otherwise the unique nearest. -/
noncomputable def roundRNE (r : ℝ) : E2M1 :=
  Classical.choose (rne_exists r)

theorem roundRNE_isRNE (r : ℝ) :
    IsRoundedToNearestEven r (roundRNE r) :=
  Classical.choose_spec (rne_exists r)

/-! ## FTZ-flushed RNE

Hardware MX accelerators may run with the FTZ flag set: any rounding
result that lands on the subnormal pattern `(e=0, m=1)` (i.e., `±0.5`
in E2M1) is replaced by `±0` post-rounding.  This is *post*-rounding
flush — the rounding decision uses the full grid first, then the
subnormal output is replaced with zero.

`roundRNE_FTZ` composes `roundRNE` with `flushSubnormal`.  It is *not*
"round to nearest in the subnormal-free grid" — those differ for `r`
near `±0.5`.  E.g., `r = 0.7`:
  *  full-grid RNE → `0.5` → FTZ flush → `0`.
  *  subnormal-free RNE → `1` (since `|0.7 - 1| < |0.7 - 0|`).
This module implements the post-rounding-flush semantics. -/

/-- FTZ-flushed RNE: round to nearest-even, then flush subnormals. -/
noncomputable def roundRNE_FTZ (r : ℝ) : E2M1 :=
  flushSubnormal (roundRNE r)

/-- `roundRNE_FTZ r` is never a subnormal pattern. -/
theorem roundRNE_FTZ_not_subnormal (r : ℝ) :
    ¬ ((roundRNE_FTZ r).e.val = 0 ∧ (roundRNE_FTZ r).m.val = 1) := by
  unfold roundRNE_FTZ flushSubnormal
  split_ifs with h
  · simp
  · exact h

/-- For inputs that don't round to a subnormal, `roundRNE_FTZ` agrees
    with `roundRNE`. -/
theorem roundRNE_FTZ_eq_roundRNE (r : ℝ)
    (h : ¬ ((roundRNE r).e.val = 0 ∧ (roundRNE r).m.val = 1)) :
    roundRNE_FTZ r = roundRNE r :=
  flushSubnormal_not_subnormal _ h

/-- For inputs whose RNE result is the subnormal pattern, FTZ produces
    `±0` (preserving the sign of the RNE result). -/
theorem roundRNE_FTZ_toReal_zero_of_subnormal (r : ℝ)
    (h : (roundRNE r).e.val = 0 ∧ (roundRNE r).m.val = 1) :
    (roundRNE_FTZ r).toReal = 0 := by
  unfold roundRNE_FTZ
  rw [flushSubnormal_toReal, if_pos h]

/-! ## Per-element RNE error bound

For `|r| < overflowBoundary = 7`, `roundRNE(r)` is within 1 of `r`.
The bound is tight at `r = ±5` (the midpoint between `±4` and `±6`,
where the largest in-range gap of 2 sits).

The proof exhibits an explicit witness `y : E2M1` from
`{0, ±2, ±4, ±6}` at distance `≤ 1` from `r`, then uses the RNE
nearest-property to conclude `|roundRNE(r).toReal - r| ≤ |y - r| ≤ 1`. -/

/-- For any in-range `r`, some E2M1 value sits within distance 1.
    Witnesses are drawn from the "even integer" sub-grid
    `{0, ±2, ±4, ±6}` whose unit balls cover `[-7, 7]`. -/
private lemma exists_E2M1_within_one (r : ℝ) (h_in : |r| < overflowBoundary) :
    ∃ y : E2M1, |y.toReal - r| ≤ 1 := by
  unfold overflowBoundary at h_in
  rcases le_or_gt 0 r with hr | hr
  · rw [abs_of_nonneg hr] at h_in
    rcases le_or_gt r 1 with h1 | h1
    · exact ⟨⟨false, 0, 0⟩, by
        rw [toReal_pos_zero, abs_le]; refine ⟨?_, ?_⟩ <;> linarith⟩
    rcases le_or_gt r 3 with h3 | h3
    · exact ⟨⟨false, 2, 0⟩, by
        rw [toReal_pos_two, abs_le]; refine ⟨?_, ?_⟩ <;> linarith⟩
    rcases le_or_gt r 5 with h5 | h5
    · exact ⟨⟨false, 3, 0⟩, by
        rw [toReal_pos_four, abs_le]; refine ⟨?_, ?_⟩ <;> linarith⟩
    · exact ⟨⟨false, 3, 1⟩, by
        rw [toReal_pos_six, abs_le]; refine ⟨?_, ?_⟩ <;> linarith⟩
  · rw [abs_of_neg hr] at h_in
    rcases le_or_gt (-1) r with h1 | h1
    · exact ⟨⟨false, 0, 0⟩, by
        rw [toReal_pos_zero, abs_le]; refine ⟨?_, ?_⟩ <;> linarith⟩
    rcases le_or_gt (-3) r with h3 | h3
    · refine ⟨⟨true, 2, 0⟩, ?_⟩
      have htwo : ((⟨true, 2, 0⟩ : E2M1)).toReal = -2 := by
        unfold toReal bias; norm_num
      rw [htwo, abs_le]; refine ⟨?_, ?_⟩ <;> linarith
    rcases le_or_gt (-5) r with h5 | h5
    · refine ⟨⟨true, 3, 0⟩, ?_⟩
      have hfour : ((⟨true, 3, 0⟩ : E2M1)).toReal = -4 := by
        unfold toReal bias; norm_num
      rw [hfour, abs_le]; refine ⟨?_, ?_⟩ <;> linarith
    · exact ⟨⟨true, 3, 1⟩, by
        rw [toReal_neg_six, abs_le]; refine ⟨?_, ?_⟩ <;> linarith⟩

/-- **Per-element RNE error bound.**  For `|r| < overflowBoundary`,
    the RNE-rounded value differs from `r` by at most 1.

    Tight at `r = ±5`, where `roundRNE(r) = ±4` (RNE tie-break) and
    `|±4 - ±5| = 1`. -/
theorem roundRNE_error_bound (r : ℝ) (h_in : |r| < overflowBoundary) :
    |(roundRNE r).toReal - r| ≤ 1 := by
  obtain ⟨y, hy⟩ := exists_E2M1_within_one r h_in
  have ⟨hmin, _⟩ := (roundRNE_isRNE r).2 h_in
  exact le_trans (hmin y) hy

end E2M1
end MX
