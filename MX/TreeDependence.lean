import MX.GEMM_FP32
import Mathlib.Tactic.FinCases

/-! # Tree-dependence over fp accumulators

`MX/Reduction.lean`'s `dotBlockedTree_tree_irrelevant_over_reals`
proves a positive result *over ℝ*: any two valid sum-trees produce
the same value, because addition over the reals is associative.

This module is its negative counterpart over fp.  We exhibit two
specific reduction trees over `IEEEFloat 8 23` (FP32) — left-fold
and right-fold over three inputs — and show they disagree on a
witness input.  The disagreement is the formal counterpart of the
Thinking Machines blog post's central observation: bit-level batch
invariance requires the kernel to commit to a specific reduction
shape, because over fp accumulators "the order in which we add
matters".

## Layout

  *  `leftFoldTree3` / `rightFoldTree3` — the two `ReductionTree`
     shapes, parameterized by an arbitrary binary `add` so the
     structural argument is not tied to any particular Acc type.
  *  `leftFoldTree3_eq_rightFoldTree3_of_assoc` — over an
     associative `add`, the two trees agree.  Specializes the ℝ-side
     `dotBlockedTree_tree_irrelevant_over_reals` to this concrete
     pair of trees.
  *  `assoc_iff_leftFoldTree3_eq_rightFoldTree3` — the equivalence:
     associativity of `add` ⇔ left-fold = right-fold on every input.
     One direction makes the negative counterpart automatic: any
     associativity counterexample lifts to a tree-disagreement
     witness.
  *  `leftFoldTree3_ne_rightFoldTree3_of_not_assoc` — the lift.
  *  `fp32_add_not_assoc` — non-associativity of FP32 addition.  The
     blog's "fp non-associativity" claim, formal.  The witness uses
     overflow: `(2^127 + 2^127) + (-2^127) = +∞ + (-2^127) = +∞`,
     but `2^127 + (2^127 + (-2^127)) = 2^127 + 0 = 2^127`.
  *  `leftFoldTree3_ne_rightFoldTree3_FP32` — the headline negative
     result, the contrapositive of Property 5 over FP32.

## Why overflow as the witness

The textbook fp non-associativity examples (`(1 + ε) + ε` vs `1 +
(ε + ε)` at half-ULP) are sharper but require pinning down the
exact tie-break behavior of `roundToNearestEven` at a half-ULP
boundary.  The overflow witness instead leans only on the IEEE 754
§4.3.1 overflow clause already encoded in `IsRoundedToNearestEven`,
plus the `inf + finite = inf` clause already encoded in
`IsCorrectlyRoundedAdd`.  Both are stated lemmas in the upstream
`IEEEFloat` library; we don't have to reach into the RNE
tie-breaking layer.
-/

namespace MX

namespace ReductionTree

variable {Acc : Type*}

/-- Left-associated 3-ary reduction: `(f 0 + f 1) + f 2`. -/
def leftFoldTree3 (add : Acc → Acc → Acc) : ReductionTree Acc 3 :=
  fun f => add (add (f 0) (f 1)) (f 2)

/-- Right-associated 3-ary reduction: `f 0 + (f 1 + f 2)`. -/
def rightFoldTree3 (add : Acc → Acc → Acc) : ReductionTree Acc 3 :=
  fun f => add (f 0) (add (f 1) (f 2))

/-- If `add` is associative, left-fold and right-fold agree on every input. -/
theorem leftFoldTree3_eq_rightFoldTree3_of_assoc
    {add : Acc → Acc → Acc}
    (h : ∀ a b c : Acc, add (add a b) c = add a (add b c))
    (f : Fin 3 → Acc) :
    leftFoldTree3 add f = rightFoldTree3 add f := by
  unfold leftFoldTree3 rightFoldTree3
  exact h _ _ _

/-- Conversely, if left-fold and right-fold agree on every input, `add` is
    associative on every triple.  The witness is `f := ![a, b, c]`. -/
theorem assoc_of_leftFoldTree3_eq_rightFoldTree3
    {add : Acc → Acc → Acc}
    (h : ∀ f : Fin 3 → Acc, leftFoldTree3 add f = rightFoldTree3 add f)
    (a b c : Acc) :
    add (add a b) c = add a (add b c) := by
  have := h ![a, b, c]
  unfold leftFoldTree3 rightFoldTree3 at this
  simpa using this

/-- Direct lift: a triple on which `add` is non-associative is a triple
    on which the two trees disagree. -/
theorem leftFoldTree3_ne_rightFoldTree3_of_not_assoc
    {add : Acc → Acc → Acc}
    {a b c : Acc} (h : add (add a b) c ≠ add a (add b c)) :
    leftFoldTree3 add ![a, b, c] ≠ rightFoldTree3 add ![a, b, c] := by
  unfold leftFoldTree3 rightFoldTree3
  simpa using h

end ReductionTree

/-! ## FP32 instance: non-associativity via overflow -/

open ReductionTree

/-- The FP32 representation of `2^127`: biased exponent 254 (= 127 + 127),
    mantissa 0, sign bit clear. -/
def twoTo127 : IEEEFloat 8 23 := .finite false ⟨254, by decide⟩ ⟨0, by decide⟩

/-- The FP32 representation of `-2^127`. -/
def negTwoTo127 : IEEEFloat 8 23 := .finite true ⟨254, by decide⟩ ⟨0, by decide⟩

theorem twoTo127_toReal : twoTo127.toRealOrZero = (2 : ℝ) ^ (127 : Int) := by
  unfold twoTo127 IEEEFloat.toRealOrZero IEEEFloat.finiteValue
  simp [IEEEFloat.bias]

theorem negTwoTo127_toReal : negTwoTo127.toRealOrZero = -(2 : ℝ) ^ (127 : Int) := by
  unfold negTwoTo127 IEEEFloat.toRealOrZero IEEEFloat.finiteValue
  simp [IEEEFloat.bias]

theorem twoTo127_isFinite : twoTo127.isFinite = true := by
  unfold twoTo127 IEEEFloat.isFinite
  rfl

/-! ### FP32 non-associativity witness

The structural argument above reduces fp32 tree-dependence to a
single fact: that `addFP32` is not associative on the triple
`(2^127, 2^127, -2^127)`.  Concretely:

  *  `a := 2^127` (FP32: sign 0, biased exp 254, mantissa 0)
  *  `b := 2^127`
  *  `c := -2^127` (FP32: sign 1, biased exp 254, mantissa 0)

Real-valued: `a + b = 2^128 ≥ overflowBoundary 8 23 = 2^128 - 2^103`,
so `addFP32 a b = +∞` per IEEE 754 §4.3.1.  Then
`addFP32 (+∞) c = +∞` per the `inf + finite` case of `IEEEFloat.add`.
Conversely, `b + c = 0` exactly, `addFP32 b c` is some finite zero,
and `addFP32 a (zero) = roundToNearestEven _ _ 2^127`, finite.  So
the LHS is `+∞` and the RHS is finite — distinct floats. -/

/-- The FP32 overflow boundary, in arithmetic-friendly form.  Uses
    `Binary32.maxFinite_eq` and `Binary32.topUlp_eq` from upstream
    to avoid `Nat`/`Int` coercion mismatches that bite raw
    `unfold`-based proofs. -/
theorem overflowBoundary_FP32_eq :
    IEEEFloat.overflowBoundary 8 23
      = (2 - (2:ℝ)^(-(23:Int))) * (2:ℝ)^(127:Int)
        + (2:ℝ)^((127:Int) - 23) / 2 := by
  unfold IEEEFloat.overflowBoundary
  rw [IEEEFloat.Binary32.maxFinite_eq, IEEEFloat.Binary32.topUlp_eq]

/-- The FP32 overflow boundary is positive. -/
theorem overflowBoundary_FP32_pos :
    (0 : ℝ) < IEEEFloat.overflowBoundary 8 23 := by
  rw [overflowBoundary_FP32_eq]
  have h1 : (2:ℝ)^(-(23:Int)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
  have h2 : (0:ℝ) < (2:ℝ)^(127:Int) := zpow_pos (by norm_num) _
  have h3 : (0:ℝ) < (2:ℝ)^((127:Int) - 23) := zpow_pos (by norm_num) _
  nlinarith [h1, h2, h3]

/-- The FP32 overflow boundary is strictly below `2^128`.  Used by the
    overflow case of RNE on `2^127 + 2^127 = 2^128`. -/
theorem overflowBoundary_FP32_lt_twoTo128 :
    IEEEFloat.overflowBoundary 8 23 < (2 : ℝ) ^ (128 : Int) := by
  rw [overflowBoundary_FP32_eq]
  have h_eq1 : (2:ℝ)^(-(23:Int)) * (2:ℝ)^(127:Int) = (2:ℝ)^((127:Int) - 23) := by
    rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]; norm_num
  have h_eq2 : (2:ℝ)^(128:Int) = 2 * (2:ℝ)^(127:Int) := by
    rw [show (128:Int) = 1 + 127 from rfl,
        zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
    simp
  have h3_pos : (0:ℝ) < (2:ℝ)^((127:Int) - 23) := zpow_pos (by norm_num) _
  -- LHS = (2 - 2^(-23)) * 2^127 + 2^(127-23) / 2
  --     = 2 * 2^127 - 2^(-23) * 2^127 + 2^(127-23) / 2
  --     = 2^128 - 2^(127-23) + 2^(127-23) / 2
  --     = 2^128 - 2^(127-23) / 2 < 2^128
  nlinarith [h_eq1, h_eq2, h3_pos]

/-- The real value of `twoTo127 + twoTo127`. -/
theorem twoTo127_add_self_real_eq :
    IEEEFloat.finiteValue (eb := 8) (mb := 23) false ⟨254, by decide⟩ ⟨0, by decide⟩
      + IEEEFloat.finiteValue (eb := 8) (mb := 23) false ⟨254, by decide⟩ ⟨0, by decide⟩
      = (2 : ℝ) ^ (128 : Int) := by
  unfold IEEEFloat.finiteValue
  have h_eq2 : (2:ℝ)^(128:Int) = 2 * (2:ℝ)^(127:Int) := by
    rw [show (128:Int) = 1 + 127 from rfl,
        zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
    simp
  simp [IEEEFloat.bias]
  linarith

/-- The real value of `twoTo127 + negTwoTo127` is exactly `0`. -/
theorem twoTo127_add_negTwoTo127_real_eq :
    IEEEFloat.finiteValue (eb := 8) (mb := 23) false ⟨254, by decide⟩ ⟨0, by decide⟩
      + IEEEFloat.finiteValue (eb := 8) (mb := 23) true  ⟨254, by decide⟩ ⟨0, by decide⟩
      = (0 : ℝ) := by
  unfold IEEEFloat.finiteValue
  simp [IEEEFloat.bias]

/-- `addFP32 twoTo127 twoTo127 = .inf false`.  Direct application of
    the RNE overflow clause, since `2^128 > overflowBoundary 8 23`. -/
theorem addFP32_twoTo127_twoTo127 :
    addFP32 twoTo127 twoTo127 = (.inf false : IEEEFloat 8 23) := by
  -- Reduce `addFP32` and the `IEEEFloat.add` `match` to the body of
  -- the `.finite, .finite` branch by `rfl`.
  show IEEEFloat.roundToNearestEven (eb := 8) (mb := 23) (by decide) (by decide)
       (IEEEFloat.finiteValue (eb := 8) (mb := 23) false ⟨254, by decide⟩ ⟨0, by decide⟩
        + IEEEFloat.finiteValue (eb := 8) (mb := 23) false ⟨254, by decide⟩ ⟨0, by decide⟩)
       = .inf false
  rw [twoTo127_add_self_real_eq]
  -- Now apply the RNE overflow clause.
  have h_isRNE := IEEEFloat.roundToNearestEven_isRNE
    (eb := 8) (mb := 23) (by decide) (by decide) ((2:ℝ)^(128:Int))
  have h_pos : (0 : ℝ) ≤ (2 : ℝ) ^ (128 : Int) :=
    le_of_lt (zpow_pos (by norm_num) _)
  have h_abs : |(2 : ℝ) ^ (128 : Int)| = (2 : ℝ) ^ (128 : Int) :=
    abs_of_nonneg h_pos
  have h_over : IEEEFloat.overflowBoundary 8 23 ≤ |(2 : ℝ) ^ (128 : Int)| := by
    rw [h_abs]; exact le_of_lt overflowBoundary_FP32_lt_twoTo128
  exact (h_isRNE.1 h_over).1 h_pos

/-- `addFP32 (.inf false) (any finite) = .inf false`.  Direct from
    the `inf + finite` case of `IEEEFloat.add`. -/
theorem addFP32_inf_false_finite (s : Bool) (e : Fin (2^8 - 1)) (m : Fin (2^23)) :
    addFP32 (.inf false) (.finite s e m) = (.inf false : IEEEFloat 8 23) := rfl

/-- `addFP32 twoTo127 negTwoTo127` is finite.  RNE of `0` produces a
    finite encoding (some zero) since `|0| < overflowBoundary`. -/
theorem addFP32_twoTo127_negTwoTo127_isFinite :
    (addFP32 twoTo127 negTwoTo127).isFinite = true := by
  show (IEEEFloat.roundToNearestEven (eb := 8) (mb := 23) (by decide) (by decide)
        (IEEEFloat.finiteValue (eb := 8) (mb := 23) false ⟨254, by decide⟩ ⟨0, by decide⟩
         + IEEEFloat.finiteValue (eb := 8) (mb := 23) true  ⟨254, by decide⟩ ⟨0, by decide⟩)
        ).isFinite = true
  rw [twoTo127_add_negTwoTo127_real_eq]
  have h_isRNE := IEEEFloat.roundToNearestEven_isRNE
    (eb := 8) (mb := 23) (by decide) (by decide) (0 : ℝ)
  have h_in_range : |(0 : ℝ)| < IEEEFloat.overflowBoundary 8 23 := by
    rw [abs_zero]; exact overflowBoundary_FP32_pos
  exact (h_isRNE.2 h_in_range).1

/-- `addFP32 twoTo127 negTwoTo127` has real value `0`.  RNE selects a
    finite encoding at minimum distance from `0`; that minimum
    distance is `0` (achieved by either `.finite false 0 0` or
    `.finite true 0 0`), so the result has `toRealOrZero = 0`. -/
theorem addFP32_twoTo127_negTwoTo127_toReal :
    (addFP32 twoTo127 negTwoTo127).toRealOrZero = 0 := by
  -- Reduce to RNE-of-0.
  show (IEEEFloat.roundToNearestEven (eb := 8) (mb := 23) (by decide) (by decide)
        (IEEEFloat.finiteValue (eb := 8) (mb := 23) false ⟨254, by decide⟩ ⟨0, by decide⟩
         + IEEEFloat.finiteValue (eb := 8) (mb := 23) true  ⟨254, by decide⟩ ⟨0, by decide⟩)
        ).toRealOrZero = 0
  rw [twoTo127_add_negTwoTo127_real_eq]
  -- Use the RNE-nearest clause with witness `.finite false 0 0` (which has
  -- `toRealOrZero = 0`, hence distance 0 to the input `0`).
  have h_isRNE := IEEEFloat.roundToNearestEven_isRNE
    (eb := 8) (mb := 23) (by decide) (by decide) (0 : ℝ)
  have h_in_range : |(0 : ℝ)| < IEEEFloat.overflowBoundary 8 23 := by
    rw [abs_zero]; exact overflowBoundary_FP32_pos
  let zero32 : IEEEFloat 8 23 := .finite false ⟨0, by decide⟩ ⟨0, by decide⟩
  have h_zero_fin : zero32.isFinite = true := rfl
  have h_zero_real : zero32.toRealOrZero = 0 := by
    show IEEEFloat.finiteValue false (⟨0, by decide⟩ : Fin (2^8 - 1))
          (⟨0, by decide⟩ : Fin (2^23)) = 0
    unfold IEEEFloat.finiteValue; simp
  -- Distance from RNE-result to 0 ≤ distance from zero32 to 0 = 0.
  have h_min := (h_isRNE.2 h_in_range).2.1 zero32 h_zero_fin
  rw [h_zero_real] at h_min
  -- |0 - 0| = 0, so |result - 0| ≤ 0, i.e., = 0.
  set r : ℝ := (IEEEFloat.roundToNearestEven (eb := 8) (mb := 23)
                  (by decide) (by decide) 0).toRealOrZero with hr
  have h_abs_zero : |((0 : ℝ)) - 0| = 0 := by simp
  rw [h_abs_zero] at h_min
  have h_abs_zero2 : |r - 0| = 0 :=
    le_antisymm h_min (abs_nonneg _)
  have h_eq : r - 0 = 0 := abs_eq_zero.mp h_abs_zero2
  linarith

/-- `addFP32 twoTo127 X` is finite when `X.isFinite = true` and
    `X.toRealOrZero = 0`.  RNE of `2^127` is finite (in range).  -/
theorem addFP32_twoTo127_finite_zero_isFinite
    (x : IEEEFloat 8 23) (hx_fin : x.isFinite = true) (hx_zero : x.toRealOrZero = 0) :
    (addFP32 twoTo127 x).isFinite = true := by
  cases x with
  | nan => simp [IEEEFloat.isFinite] at hx_fin
  | inf _ => simp [IEEEFloat.isFinite] at hx_fin
  | finite s e m =>
    show (IEEEFloat.roundToNearestEven (eb := 8) (mb := 23) (by decide) (by decide)
           (IEEEFloat.finiteValue (eb := 8) (mb := 23) false ⟨254, by decide⟩ ⟨0, by decide⟩
            + IEEEFloat.finiteValue (eb := 8) (mb := 23) s e m)).isFinite = true
    have h_x_real : IEEEFloat.finiteValue (eb := 8) (mb := 23) s e m = 0 := by
      simpa [IEEEFloat.toRealOrZero] using hx_zero
    rw [h_x_real, add_zero]
    -- Goal: (RNE _ _ (finiteValue false 254 0)).isFinite = true.  This real
    -- value is 2^127, well within range.
    have h_real_eq : IEEEFloat.finiteValue (eb := 8) (mb := 23)
                        false ⟨254, by decide⟩ ⟨0, by decide⟩ = (2:ℝ)^(127:Int) := by
      unfold IEEEFloat.finiteValue
      simp [IEEEFloat.bias]
    rw [h_real_eq]
    have h_isRNE := IEEEFloat.roundToNearestEven_isRNE
      (eb := 8) (mb := 23) (by decide) (by decide) ((2:ℝ)^(127:Int))
    have h_in_range : |(2:ℝ)^(127:Int)| < IEEEFloat.overflowBoundary 8 23 := by
      rw [abs_of_pos (zpow_pos (by norm_num) _)]
      -- 2^127 < overflowBoundary = (almost) 2^128.
      -- overflowBoundary = (2 - 2^-23) * 2^127 + 2^(127-23)/2
      --                  > (2 - 1) * 2^127 = 2^127.
      rw [overflowBoundary_FP32_eq]
      have h1 : (2:ℝ)^(-(23:Int)) ≤ 1 :=
        zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
      have h2 : (0:ℝ) < (2:ℝ)^(127:Int) := zpow_pos (by norm_num) _
      have h3 : (0:ℝ) < (2:ℝ)^((127:Int) - 23) := zpow_pos (by norm_num) _
      nlinarith [h1, h2, h3]
    exact (h_isRNE.2 h_in_range).1

/-- IEEE 754 FP32 addition is not associative.  Witness:
    `a = b = 2^127`, `c = -2^127`. -/
theorem fp32_add_not_assoc :
    ∃ a b c : IEEEFloat 8 23,
      addFP32 (addFP32 a b) c ≠ addFP32 a (addFP32 b c) := by
  refine ⟨twoTo127, twoTo127, negTwoTo127, ?_⟩
  -- LHS reduces to `.inf false` (overflow).
  have h_lhs : addFP32 (addFP32 twoTo127 twoTo127) negTwoTo127
              = (.inf false : IEEEFloat 8 23) := by
    rw [addFP32_twoTo127_twoTo127]
    show addFP32 (.inf false) (.finite true ⟨254, by decide⟩ ⟨0, by decide⟩)
       = (.inf false : IEEEFloat 8 23)
    exact addFP32_inf_false_finite _ _ _
  -- RHS is finite.
  have h_rhs_fin : (addFP32 twoTo127 (addFP32 twoTo127 negTwoTo127)).isFinite = true :=
    addFP32_twoTo127_finite_zero_isFinite _
      addFP32_twoTo127_negTwoTo127_isFinite
      addFP32_twoTo127_negTwoTo127_toReal
  -- LHS is `.inf false`, so it's not finite.  RHS is finite.  Contradiction.
  rw [h_lhs]
  intro heq
  have : (IEEEFloat.inf false : IEEEFloat 8 23).isFinite = true := heq ▸ h_rhs_fin
  exact absurd this (by decide)

/-- **Negative counterpart of Property 5 over FP32.**  There exist
    inputs on which the left-fold and right-fold reduction trees
    disagree when evaluated over the FP32 accumulator.

    This is the contrapositive of
    `dotBlockedTree_tree_irrelevant_over_reals` — over ℝ the two
    trees always agree; over FP32 they don't.  It is what forces
    `mxGEMMAcc_batch_invariant`'s "fixed `t`" quantification: drop
    that quantification and the GEMM output ceases to be a function
    of the inputs alone.

    Concretely: any kernel that switches between left-fold and
    right-fold (or any two distinct reduction shapes — the result
    generalizes from `m=3` to all sufficiently large `m`) loses
    bit-level batch invariance.  This is exactly the diagnosis in
    the Thinking Machines blog post on LLM-inference
    nondeterminism. -/
theorem leftFoldTree3_ne_rightFoldTree3_FP32 :
    ∃ f : Fin 3 → IEEEFloat 8 23,
      leftFoldTree3 addFP32 f ≠ rightFoldTree3 addFP32 f := by
  obtain ⟨a, b, c, h⟩ := fp32_add_not_assoc
  exact ⟨![a, b, c], leftFoldTree3_ne_rightFoldTree3_of_not_assoc h⟩

end MX
