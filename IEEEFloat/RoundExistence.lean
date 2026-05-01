import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity
import IEEEFloat.Round
import IEEEFloat.Spacing

/-! # Classical existence of round-to-nearest

This module proves `∀ r : ℝ, ∃ x : IEEEFloat eb mb, IsRoundedToNearest r x`
for any format with `eb ≥ 1` (so that finite encodings exist), and
defines `roundToNearest` non-constructively via `Classical.choose`.

The proof structure is straightforward:

  *  **Overflow** (`overflowBoundary ≤ |r|`): the spec pins the
     witness — `±∞` with the sign of `r`.
  *  **In-range** (`|r| < overflowBoundary`): the set of finite
     encodings is finite (`Fintype`), nonempty (contains `+0`), and
     `Finset.exists_min_image` produces an argmin against
     `|·.toRealOrZero - r|`.

`IsRoundedToNearestEven` (with the even-mantissa tie-break) then
follows by selecting an even-mantissa witness when one exists among
the closest finites — the tie-partner of an odd-mantissa closest is
always even (by parity-alternation across encoding-adjacent values).
-/

namespace IEEEFloat

variable {eb mb : Nat}

/-- The finite IEEEFloat encodings (i.e., not NaN / not ±∞), as a Finset. -/
def finiteFinset (eb mb : Nat) : Finset (IEEEFloat eb mb) :=
  Finset.univ.filter (fun y => y.isFinite = true)

theorem mem_finiteFinset {y : IEEEFloat eb mb} :
    y ∈ finiteFinset eb mb ↔ y.isFinite = true := by
  simp [finiteFinset]

/-- For `eb ≥ 1`, positive zero is a witness that `finiteFinset` is nonempty. -/
theorem finiteFinset_nonempty (heb : 1 ≤ eb) :
    (finiteFinset eb mb).Nonempty := by
  have h_eb_carrier : 0 < 2 ^ eb - 1 := by
    have h1 : (2 : Nat) ^ 1 ≤ 2 ^ eb := Nat.pow_le_pow_right (by norm_num) heb
    have h2 : (2 : Nat) ≤ 2 ^ eb := by simpa using h1
    omega
  have h_mb_carrier : 0 < 2 ^ mb := by positivity
  refine ⟨.finite false ⟨0, h_eb_carrier⟩ ⟨0, h_mb_carrier⟩, ?_⟩
  rw [mem_finiteFinset]
  rfl

/-! ## Existence of RN

The first-class theorem of this module.  Note `eb ≥ 1` is essential:
for `eb = 0` no finite encoding exists (the carrier `Fin (2^0 - 1)
= Fin 0` is empty), so the `IsRoundedToNearest` predicate is
unsatisfiable in the in-range regime. -/

theorem rn_exists (heb : 1 ≤ eb) (r : ℝ) :
    ∃ x : IEEEFloat eb mb, IsRoundedToNearest r x := by
  by_cases hover : overflowBoundary eb mb ≤ |r|
  · by_cases hpos : 0 ≤ r
    · refine ⟨.inf false, ?_, fun hin => ?_⟩
      · intro _
        refine ⟨fun _ => rfl, fun hr => ?_⟩
        exfalso; linarith
      · exfalso; linarith
    · push_neg at hpos
      refine ⟨.inf true, ?_, fun hin => ?_⟩
      · intro _
        refine ⟨fun hr => ?_, fun _ => rfl⟩
        exfalso; linarith
      · exfalso; linarith
  · push_neg at hover
    obtain ⟨x, hx_mem, hx_min⟩ :=
      (finiteFinset eb mb).exists_min_image (fun y => |y.toRealOrZero - r|)
        (finiteFinset_nonempty heb)
    refine ⟨x, fun hcontra => ?_, fun _ => ?_⟩
    · exfalso; linarith
    · have hx_finite : x.isFinite = true := (mem_finiteFinset.mp hx_mem)
      refine ⟨hx_finite, fun y hy_finite => ?_⟩
      exact hx_min y (mem_finiteFinset.mpr hy_finite)

/-! ## The classical-choice rounding function -/

/-- Classical round-to-nearest.  Picks an arbitrary closest finite
    encoding (or `±∞` on overflow) — uniqueness modulo ±0 / RNE
    tie-breaking is **not** guaranteed by this definition. -/
noncomputable def roundToNearest (heb : 1 ≤ eb) (r : ℝ) : IEEEFloat eb mb :=
  Classical.choose (rn_exists (eb := eb) (mb := mb) heb r)

theorem roundToNearest_isRN (heb : 1 ≤ eb) (r : ℝ) :
    IsRoundedToNearest r (roundToNearest (eb := eb) (mb := mb) heb r) :=
  Classical.choose_spec (rn_exists (eb := eb) (mb := mb) heb r)

/-! ## Existence of RNE

The strengthening from `IsRoundedToNearest` to `IsRoundedToNearestEven`
hinges on a structural fact: if a finite encoding `x` ties with a
*different* encoding `y` for closest-to-`r`, and `x` has odd mantissa,
then `y` must have even mantissa.  This means the set of finite RN
witnesses always contains an even-mantissa member, so picking such a
witness satisfies the RNE tie-break clause.

The tie-partner argument is symmetric in the order of `x.value` and
`y.value`.  The asymmetric direction (`x.value < y.value`) walks
`nextFinite x` and uses encoding-adjacency + parity-alternation; the
mirror direction uses `nextFinite y`. -/

private theorem ne_zero_of_odd_mantissa
    {x : IEEEFloat eb mb} (h_odd : x.mantissaLSB = 1)
    (s : Bool) (h_e : 0 < 2 ^ eb - 1) (h_m : 0 < 2 ^ mb) :
    x ≠ (.finite s ⟨0, h_e⟩ ⟨0, h_m⟩ : IEEEFloat eb mb) := by
  intro hx
  rw [hx] at h_odd
  simp [mantissaLSB_finite] at h_odd

/-- Strict version of `nextFinite_toRealOrZero_ge`: equality is reached
    only at the encoding-level `−0 → +0` step (where both sides are 0). -/
private theorem nextFinite_toRealOrZero_lt
    (x : IEEEFloat eb mb) (h_fin : x.isFinite = true)
    (h_succ_fin : (nextFinite x).isFinite = true)
    (h_not_neg_zero : ∀ (h_e : 0 < 2 ^ eb - 1) (h_m : 0 < 2 ^ mb),
      x ≠ (.finite true ⟨0, h_e⟩ ⟨0, h_m⟩ : IEEEFloat eb mb)) :
    x.toRealOrZero < (nextFinite x).toRealOrZero := by
  match x, h_fin with
  | .finite false e m, _ =>
      simp only [nextFinite] at h_succ_fin ⊢
      split
      · rename_i h_m
        exact nextFinite_value_lt_pos_within e m h_m
      · rename_i h_m
        split
        · rename_i h_e
          exact nextFinite_value_lt_pos_cross e m h_m h_e
        · rename_i h_e
          simp [h_m, h_e, isFinite] at h_succ_fin
  | .finite true e m, _ =>
      simp only [nextFinite] at h_succ_fin ⊢
      split
      · rename_i h_m
        exact nextFinite_value_lt_neg_within e m h_m
      · rename_i h_m
        split
        · rename_i h_e
          have h_e_ne : e.val ≠ 0 := h_e
          exact nextFinite_value_lt_neg_cross e m h_m h_e_ne
        · rename_i h_e
          -- −0 → +0 case: contradicts h_not_neg_zero.
          exfalso
          push_neg at h_m h_e
          have h_zero : 0 < 2 ^ mb := Nat.pow_pos (by decide)
          have h_ez : 0 < 2 ^ eb - 1 := lt_of_le_of_lt (Nat.zero_le _) (h_e ▸ e.isLt)
          apply h_not_neg_zero h_ez h_zero
          congr 1
          · exact Fin.ext h_e
          · exact Fin.ext h_m

/-- `nextFinite a` is finite whenever there's some finite encoding strictly
    above `a` in real value.  The only case where `nextFinite a` is `+∞`
    is when `a` is the maximum positive normal — but then no finite z
    can have `z.value > a.value`. -/
private theorem nextFinite_isFinite_of_lt
    (a z : IEEEFloat eb mb) (h_a_fin : a.isFinite = true) (h_z_fin : z.isFinite = true)
    (h_lt : a.toRealOrZero < z.toRealOrZero) :
    (nextFinite a).isFinite = true := by
  match a, h_a_fin with
  | .finite false e_a m_a, _ =>
      simp only [nextFinite]
      split
      · simp [isFinite]
      · split
        · simp [isFinite]
        · -- a is at max positive normal; can't have z.value > a.value finite.
          exfalso
          rename_i h_m h_e
          push_neg at h_m h_e
          have h_m_eq : m_a.val = 2 ^ mb - 1 := by have := m_a.isLt; omega
          match z, h_z_fin with
          | .finite s_z e_z m_z, _ =>
            rw [toRealOrZero_finite_eq, toRealOrZero_finite_eq] at h_lt
            rcases s_z with - | -
            · -- z positive: trichotomy bounds z by max
              rcases (finiteValue_pos_lt_iff e_a e_z m_a m_z).mp h_lt with h_e_lt | ⟨_, h_m_lt⟩
              · have hez : e_z.val < 2 ^ eb - 1 := e_z.isLt
                omega
              · have hmz : m_z.val < 2 ^ mb := m_z.isLt
                omega
            · -- z negative: z.value ≤ 0 ≤ a.value
              have hz_np := finiteValue_neg_nonpos (eb := eb) (mb := mb) e_z m_z
              have ha_nn := finiteValue_pos_nonneg (eb := eb) (mb := mb) e_a m_a
              linarith
  | .finite true _ _, _ =>
      simp only [nextFinite]
      split
      · simp [isFinite]
      · split
        · simp [isFinite]
        · simp [isFinite]

/-- For finite `a, b` with `a.value < b.value`, `a` closest to `r` and
    equidistant with `b`, and `a ≠ −0`: `nextFinite a` matches `b` in
    real value. -/
private theorem nextFinite_eq_tied
    (a b : IEEEFloat eb mb) (h_a_fin : a.isFinite = true) (h_b_fin : b.isFinite = true)
    (h_succ_fin : (nextFinite a).isFinite = true)
    (h_a_not_neg_zero : ∀ (h_e : 0 < 2 ^ eb - 1) (h_m : 0 < 2 ^ mb),
      a ≠ (.finite true ⟨0, h_e⟩ ⟨0, h_m⟩ : IEEEFloat eb mb))
    (r : ℝ) (h_lt : a.toRealOrZero < b.toRealOrZero)
    (h_min : ∀ z : IEEEFloat eb mb, z.isFinite = true →
      |a.toRealOrZero - r| ≤ |z.toRealOrZero - r|)
    (h_dist : |a.toRealOrZero - r| = |b.toRealOrZero - r|) :
    (nextFinite a).toRealOrZero = b.toRealOrZero := by
  set d := |a.toRealOrZero - r| with hd_def
  have hd_b : |b.toRealOrZero - r| = d := h_dist.symm
  -- Step 1: equidistance + a < b ⇒ a.value ≤ r ≤ b.value.
  have ha_le_r : a.toRealOrZero ≤ r := by
    by_contra h
    push_neg at h
    have h1 : 0 < a.toRealOrZero - r := sub_pos.mpr h
    have h2 : 0 < b.toRealOrZero - r := by linarith
    have ha_abs : |a.toRealOrZero - r| = a.toRealOrZero - r := abs_of_pos h1
    have hb_abs : |b.toRealOrZero - r| = b.toRealOrZero - r := abs_of_pos h2
    have : a.toRealOrZero - r = b.toRealOrZero - r := by
      rw [← ha_abs, ← hb_abs]; exact h_dist
    linarith
  have hr_le_b : r ≤ b.toRealOrZero := by
    by_contra h
    push_neg at h
    have h1 : b.toRealOrZero - r < 0 := sub_neg.mpr h
    have h2 : a.toRealOrZero - r < 0 := by linarith
    have ha_abs : |a.toRealOrZero - r| = -(a.toRealOrZero - r) := abs_of_neg h2
    have hb_abs : |b.toRealOrZero - r| = -(b.toRealOrZero - r) := abs_of_neg h1
    have : -(a.toRealOrZero - r) = -(b.toRealOrZero - r) := by
      rw [← ha_abs, ← hb_abs]; exact h_dist
    linarith
  -- Step 2: a.value = r − d, b.value = r + d.
  have ha_eq : a.toRealOrZero = r - d := by
    have h_neg : a.toRealOrZero - r ≤ 0 := by linarith
    have h_abs : |a.toRealOrZero - r| = -(a.toRealOrZero - r) := abs_of_nonpos h_neg
    have : d = -(a.toRealOrZero - r) := by rw [hd_def]; exact h_abs
    linarith
  have hb_eq : b.toRealOrZero = r + d := by
    have h_pos : 0 ≤ b.toRealOrZero - r := by linarith
    have h_abs : |b.toRealOrZero - r| = b.toRealOrZero - r := abs_of_nonneg h_pos
    have : d = b.toRealOrZero - r := by rw [← h_abs]; exact hd_b.symm
    linarith
  -- Step 3: a.value ≤ (nextFinite a).value ≤ b.value.
  have h_succ_ge_a : a.toRealOrZero ≤ (nextFinite a).toRealOrZero :=
    nextFinite_toRealOrZero_ge a h_a_fin h_succ_fin
  have h_succ_le_b : (nextFinite a).toRealOrZero ≤ b.toRealOrZero :=
    nextFinite_encoding_adjacent a h_a_fin h_succ_fin b h_b_fin h_lt
  -- Step 4: |(nextFinite a).value − r| ≤ d (interpolation).
  have h_succ_dist_le : |(nextFinite a).toRealOrZero - r| ≤ d := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · linarith
    · linarith
  -- Step 5: minimality bounds the other direction.
  have h_succ_dist_ge : d ≤ |(nextFinite a).toRealOrZero - r| := h_min (nextFinite a) h_succ_fin
  have h_succ_dist_eq : |(nextFinite a).toRealOrZero - r| = d :=
    le_antisymm h_succ_dist_le h_succ_dist_ge
  -- Step 6: (nextFinite a).value ∈ {r + d, r − d}.
  have h_d_nn : 0 ≤ d := by rw [hd_def]; exact abs_nonneg _
  have h_nx_eq : (nextFinite a).toRealOrZero = r + d ∨ (nextFinite a).toRealOrZero = r - d := by
    rcases (abs_eq h_d_nn).mp h_succ_dist_eq with hp | hn
    · left; linarith
    · right; linarith
  -- Step 7: rule out r − d via strict monotonicity (a ≠ −0).
  rcases h_nx_eq with hp | hn
  · rw [hb_eq]; exact hp
  · exfalso
    have h_strict := nextFinite_toRealOrZero_lt a h_a_fin h_succ_fin h_a_not_neg_zero
    rw [ha_eq] at h_strict
    rw [hn] at h_strict
    exact lt_irrefl _ h_strict

/-- Tie-break helper: when `x` is a finite RN witness with odd mantissa
    and `y ≠ x` is a same-distance finite encoding, `y` has even mantissa. -/
private theorem tie_partner_is_even
    (hmb : 1 ≤ mb) (r : ℝ)
    (x y : IEEEFloat eb mb) (hx_fin : x.isFinite = true) (hy_fin : y.isFinite = true)
    (hx_min : ∀ z : IEEEFloat eb mb, z.isFinite = true →
      |x.toRealOrZero - r| ≤ |z.toRealOrZero - r|)
    (hxy_dist : |x.toRealOrZero - r| = |y.toRealOrZero - r|)
    (hxy_ne : x ≠ y)
    (hx_odd : x.mantissaLSB = 1) :
    y.mantissaLSB = 0 := by
  -- x has odd mantissa ⇒ x is neither +0 nor −0.
  have hx_not_pos_zero : ∀ (h_e : 0 < 2 ^ eb - 1) (h_m : 0 < 2 ^ mb),
      x ≠ (.finite false ⟨0, h_e⟩ ⟨0, h_m⟩ : IEEEFloat eb mb) :=
    fun h_e h_m => ne_zero_of_odd_mantissa hx_odd false h_e h_m
  have hx_not_neg_zero : ∀ (h_e : 0 < 2 ^ eb - 1) (h_m : 0 < 2 ^ mb),
      x ≠ (.finite true ⟨0, h_e⟩ ⟨0, h_m⟩ : IEEEFloat eb mb) :=
    fun h_e h_m => ne_zero_of_odd_mantissa hx_odd true h_e h_m
  -- `y` is finite, so we can destructure it.
  cases y with
  | nan => simp [isFinite] at hy_fin
  | inf _ => simp [isFinite] at hy_fin
  | finite s_y e_y m_y =>
  -- Same for x.
  cases x with
  | nan => simp [isFinite] at hx_fin
  | inf _ => simp [isFinite] at hx_fin
  | finite s_x e_x m_x =>
  -- Now both x and y are `.finite ...`.  Bridge to `finiteValue`.
  rw [toRealOrZero_finite_eq, toRealOrZero_finite_eq] at hxy_dist
  -- Case split on x.value vs y.value.
  by_cases h_eq : finiteValue (eb := eb) (mb := mb) s_x e_x m_x
                = finiteValue s_y e_y m_y
  · -- Same value: by inj mod ±0, x = y (contradicts hxy_ne) or both ±0.
    exfalso
    rcases finiteValue_inj_modulo_zero h_eq with
      ⟨hm_x_zero, _, _, _⟩ | ⟨hs_eq, he_eq, hm_eq⟩
    · -- Both ±0: x.mantissaLSB = 0, contradicts hx_odd.
      have h_lsb_zero : (IEEEFloat.finite s_x e_x m_x : IEEEFloat eb mb).mantissaLSB = 0 := by
        simp [mantissaLSB_finite, hm_x_zero]
      rw [h_lsb_zero] at hx_odd
      exact absurd hx_odd (by decide)
    · -- Same encoding: contradicts hxy_ne.
      exact hxy_ne (by rw [hs_eq, he_eq, hm_eq])
  · -- Different values.
    rcases lt_or_gt_of_ne h_eq with h_lt | h_gt
    · -- x.value < y.value: walk nextFinite from x.
      have h_lt' : (IEEEFloat.finite s_x e_x m_x : IEEEFloat eb mb).toRealOrZero
                 < (IEEEFloat.finite s_y e_y m_y : IEEEFloat eb mb).toRealOrZero := by
        rw [toRealOrZero_finite_eq, toRealOrZero_finite_eq]; exact h_lt
      have h_succ_fin : (nextFinite (.finite s_x e_x m_x : IEEEFloat eb mb)).isFinite = true :=
        nextFinite_isFinite_of_lt _ _ hx_fin hy_fin h_lt'
      have h_eq_y : (nextFinite (.finite s_x e_x m_x : IEEEFloat eb mb)).toRealOrZero
                  = (IEEEFloat.finite s_y e_y m_y : IEEEFloat eb mb).toRealOrZero :=
        nextFinite_eq_tied _ _ hx_fin hy_fin h_succ_fin hx_not_neg_zero r h_lt'
          hx_min (by rw [toRealOrZero_finite_eq, toRealOrZero_finite_eq]; exact hxy_dist)
      -- Destructure nextFinite x, then use injection mod ±0.
      obtain ⟨s_n, e_n, m_n, h_n_eq⟩ :
          ∃ s e m, (nextFinite (.finite s_x e_x m_x : IEEEFloat eb mb)) = .finite s e m := by
        match h_n : (nextFinite (.finite s_x e_x m_x : IEEEFloat eb mb)) with
        | .nan => rw [h_n] at h_succ_fin; simp [isFinite] at h_succ_fin
        | .inf _ => rw [h_n] at h_succ_fin; simp [isFinite] at h_succ_fin
        | .finite s e m => exact ⟨s, e, m, rfl⟩
      rw [h_n_eq, toRealOrZero_finite_eq, toRealOrZero_finite_eq] at h_eq_y
      rcases finiteValue_inj_modulo_zero h_eq_y with
        ⟨_, hm_y_zero, _, _⟩ | ⟨hs_eq, he_eq, hm_eq⟩
      · -- y is ±0: mantissaLSB = 0.
        simp [mantissaLSB_finite, hm_y_zero]
      · -- nextFinite x = y as encoding.  Apply parity alternation.
        have h_alt :=
          nextFinite_mantissaLSB_diff_or_zero (.finite s_x e_x m_x : IEEEFloat eb mb)
            hx_fin h_succ_fin hmb
        -- Rewrite (nextFinite x).mantissaLSB = (.finite s_n e_n m_n).mantissaLSB
        --   = (.finite s_y e_y m_y).mantissaLSB (using hs_eq/he_eq/hm_eq).
        rw [h_n_eq] at h_alt
        rw [show (IEEEFloat.finite s_n e_n m_n : IEEEFloat eb mb)
              = .finite s_y e_y m_y from by rw [hs_eq, he_eq, hm_eq]] at h_alt
        rcases h_alt with h_ne | ⟨h_x_zero, _⟩
        · -- mantissaLSB x = 1, h_ne ⇒ mantissaLSB y ≠ 1.  mantissaLSB ∈ {0, 1}.
          rw [hx_odd] at h_ne
          have h_y_lsb_lt2 :
              (IEEEFloat.finite s_y e_y m_y : IEEEFloat eb mb).mantissaLSB < 2 := by
            rw [mantissaLSB_finite]; exact Nat.mod_lt _ (by decide)
          omega
        · -- "both 0" disjunct.
          rw [hx_odd] at h_x_zero
          exact absurd h_x_zero (by decide)
    · -- y.value < x.value.  Either y is ±0 (lsb = 0 directly) or apply
      -- nextFinite_eq_tied with a := y, b := x.
      by_cases h_y_is_zero : m_y.val = 0 ∧ e_y.val = 0
      · obtain ⟨hm, _⟩ := h_y_is_zero
        simp [mantissaLSB_finite, hm]
      · -- y ≠ ±0.
        have hy_not_neg_zero : ∀ (h_e : 0 < 2 ^ eb - 1) (h_m : 0 < 2 ^ mb),
            (IEEEFloat.finite s_y e_y m_y : IEEEFloat eb mb)
              ≠ (.finite true ⟨0, h_e⟩ ⟨0, h_m⟩ : IEEEFloat eb mb) := by
          intro h_e h_m h
          apply h_y_is_zero
          cases h
          exact ⟨rfl, rfl⟩
        have h_gt' : (IEEEFloat.finite s_y e_y m_y : IEEEFloat eb mb).toRealOrZero
                   < (IEEEFloat.finite s_x e_x m_x : IEEEFloat eb mb).toRealOrZero := by
          rw [toRealOrZero_finite_eq, toRealOrZero_finite_eq]; exact h_gt
        have h_succ_fin :
            (nextFinite (.finite s_y e_y m_y : IEEEFloat eb mb)).isFinite = true :=
          nextFinite_isFinite_of_lt _ _ hy_fin hx_fin h_gt'
        have hy_min : ∀ z : IEEEFloat eb mb, z.isFinite = true →
            |(IEEEFloat.finite s_y e_y m_y : IEEEFloat eb mb).toRealOrZero - r|
              ≤ |z.toRealOrZero - r| := by
          intro z hz
          rw [toRealOrZero_finite_eq, ← hxy_dist]
          exact hx_min z hz
        have h_eq_x : (nextFinite (.finite s_y e_y m_y : IEEEFloat eb mb)).toRealOrZero
                    = (IEEEFloat.finite s_x e_x m_x : IEEEFloat eb mb).toRealOrZero :=
          nextFinite_eq_tied _ _ hy_fin hx_fin h_succ_fin hy_not_neg_zero r h_gt' hy_min
            (by rw [toRealOrZero_finite_eq, toRealOrZero_finite_eq]; exact hxy_dist.symm)
        obtain ⟨s_n, e_n, m_n, h_n_eq⟩ :
            ∃ s e m, (nextFinite (.finite s_y e_y m_y : IEEEFloat eb mb)) = .finite s e m := by
          match h_n : (nextFinite (.finite s_y e_y m_y : IEEEFloat eb mb)) with
          | .nan => rw [h_n] at h_succ_fin; simp [isFinite] at h_succ_fin
          | .inf _ => rw [h_n] at h_succ_fin; simp [isFinite] at h_succ_fin
          | .finite s e m => exact ⟨s, e, m, rfl⟩
        rw [h_n_eq, toRealOrZero_finite_eq, toRealOrZero_finite_eq] at h_eq_x
        rcases finiteValue_inj_modulo_zero h_eq_x with
          ⟨_, hm_x_zero, _, _⟩ | ⟨hs_eq, he_eq, hm_eq⟩
        · -- x is ±0: but x has odd mantissa.  Contradiction.
          exfalso
          have h_lsb_zero : (IEEEFloat.finite s_x e_x m_x : IEEEFloat eb mb).mantissaLSB = 0 := by
            simp [mantissaLSB_finite, hm_x_zero]
          rw [h_lsb_zero] at hx_odd
          exact absurd hx_odd (by decide)
        · -- nextFinite y = x as encoding.  Use parity alternation at y.
          have h_alt :=
            nextFinite_mantissaLSB_diff_or_zero
              (.finite s_y e_y m_y : IEEEFloat eb mb) hy_fin h_succ_fin hmb
          rw [h_n_eq] at h_alt
          rw [show (IEEEFloat.finite s_n e_n m_n : IEEEFloat eb mb)
                = .finite s_x e_x m_x from by rw [hs_eq, he_eq, hm_eq]] at h_alt
          rcases h_alt with h_ne | ⟨_, h_x_zero⟩
          · -- y.mantissaLSB ≠ x.mantissaLSB = 1; mantissaLSB ∈ {0, 1}.
            rw [hx_odd] at h_ne
            have h_y_lsb_lt2 :
                (IEEEFloat.finite s_y e_y m_y : IEEEFloat eb mb).mantissaLSB < 2 := by
              rw [mantissaLSB_finite]; exact Nat.mod_lt _ (by decide)
            omega
          · -- "both 0" disjunct, but x has odd mantissa.
            rw [hx_odd] at h_x_zero
            exact absurd h_x_zero (by decide)

/-- Existence of round-to-nearest-even.  Constructs an RNE witness by
    starting from any RN witness and either using it directly (when
    even, or when no tie partner exists) or swapping in its tie
    partner (which `tie_partner_is_even` guarantees has even mantissa). -/
theorem rne_exists (heb : 1 ≤ eb) (hmb : 1 ≤ mb) (r : ℝ) :
    ∃ x : IEEEFloat eb mb, IsRoundedToNearestEven r x := by
  obtain ⟨x_0, hx_0_rn⟩ := rn_exists (eb := eb) (mb := mb) heb r
  by_cases hover : overflowBoundary eb mb ≤ |r|
  · -- Overflow: x_0 is .inf with sign of r; in-range obligation is vacuous.
    refine ⟨x_0, hx_0_rn.1, fun hr => ?_⟩
    exfalso; linarith
  · push_neg at hover
    obtain ⟨hx_0_fin, hx_0_min⟩ := hx_0_rn.2 hover
    -- Build the witness by case analysis.
    by_cases h_x_0_even : x_0.mantissaLSB = 0
    · -- x_0 is even: works as RNE witness.
      refine ⟨x_0, fun h => (absurd hover (not_lt.mpr h)), fun _ => ?_⟩
      refine ⟨hx_0_fin, hx_0_min, ?_⟩
      intro y _ _ _
      cases x_0 with
      | nan => simp [isFinite] at hx_0_fin
      | inf _ => simp [isFinite] at hx_0_fin
      | finite s e m =>
        refine ⟨s, e, m, rfl, ?_⟩
        simp [mantissaLSB_finite] at h_x_0_even
        exact h_x_0_even
    · -- x_0 is odd.  Look for a tie partner.
      classical
      by_cases h_has_tie :
          ∃ y : IEEEFloat eb mb, y.isFinite = true ∧ y ≠ x_0 ∧
            |x_0.toRealOrZero - r| = |y.toRealOrZero - r|
      · -- Tie partner exists.  Swap to it; it has even mantissa.
        obtain ⟨y_0, hy_0_fin, hy_0_ne, hy_0_dist⟩ := h_has_tie
        have h_x_0_lsb_lt2 : x_0.mantissaLSB < 2 := by
          cases x_0 with
          | nan => simp [isFinite] at hx_0_fin
          | inf _ => simp [isFinite] at hx_0_fin
          | finite _ _ _ => simp [mantissaLSB_finite]; exact Nat.mod_lt _ (by decide)
        have h_x_0_odd : x_0.mantissaLSB = 1 := by omega
        have hy_0_even := tie_partner_is_even hmb r x_0 y_0 hx_0_fin hy_0_fin
          hx_0_min hy_0_dist hy_0_ne.symm h_x_0_odd
        refine ⟨y_0, fun h => (absurd hover (not_lt.mpr h)), fun _ => ?_⟩
        refine ⟨hy_0_fin, ?_, ?_⟩
        · -- y_0 is closest: |y_0 - r| = |x_0 - r| ≤ |z - r|.
          intro z hz
          rw [← hy_0_dist]; exact hx_0_min z hz
        · intro z _ _ _
          cases y_0 with
          | nan => simp [isFinite] at hy_0_fin
          | inf _ => simp [isFinite] at hy_0_fin
          | finite s e m =>
            refine ⟨s, e, m, rfl, ?_⟩
            simp [mantissaLSB_finite] at hy_0_even
            exact hy_0_even
      · -- No tie partner: x_0 satisfies RNE vacuously.
        push_neg at h_has_tie
        refine ⟨x_0, fun h => (absurd hover (not_lt.mpr h)), fun _ => ?_⟩
        refine ⟨hx_0_fin, hx_0_min, ?_⟩
        intro y hy_fin hy_ne hy_dist
        exfalso
        exact h_has_tie y hy_fin hy_ne hy_dist

/-- Classical round-to-nearest-even. -/
noncomputable def roundToNearestEven (heb : 1 ≤ eb) (hmb : 1 ≤ mb) (r : ℝ) :
    IEEEFloat eb mb :=
  Classical.choose (rne_exists (eb := eb) (mb := mb) heb hmb r)

theorem roundToNearestEven_isRNE (heb : 1 ≤ eb) (hmb : 1 ≤ mb) (r : ℝ) :
    IsRoundedToNearestEven r (roundToNearestEven (eb := eb) (mb := mb) heb hmb r) :=
  Classical.choose_spec (rne_exists (eb := eb) (mb := mb) heb hmb r)

end IEEEFloat
