import Mathlib.Algebra.BigOperators.Ring.Finset
import MX.Dot
import MX.Round
import MX.Softmax

/-! # Roadmap theorem exemplars

This module collects small, compile-checked theorem entry points for the
roadmap examples in `ROADMAP.md`.  These are intentionally lightweight:
they give downstream modules stable names to strengthen as the bitwise,
relational, and probabilistic-affine models grow.
-/

namespace MX
namespace Roadmap

namespace RelSem

/-- A generic refinement contract: `round` refines `rel` when every real
input is related to the rounded output. -/
def RoundingRefines {α : Type*} (round : ℝ → α) (rel : ℝ → α → Prop) : Prop :=
  ∀ x, rel x (round x)

/-- Add a constant shift to every coordinate of a finite real vector. -/
def shift {K : Nat} (x : Fin K → ℝ) (c : ℝ) : Fin K → ℝ :=
  fun i => x i + c

/-- A semantic function is shift-invariant when uniform logit shifts do
not change its result.  Real softmax should instantiate this relation. -/
def ShiftInvariant {K : Nat} {α : Type*} (f : (Fin K → ℝ) → α) : Prop :=
  ∀ x c, f (shift x c) = f x

/-- Roadmap exemplar: semantic softmax is invariant under uniform logit
shifts.  The concrete real-softmax instantiation is future work; this
theorem fixes the relation shape used by that proof. -/
theorem softmax_shift_invariant_rel {K : Nat} {α : Type*}
    (softmax : (Fin K → ℝ) → α)
    (h : ShiftInvariant softmax) :
    ∀ x c, softmax (shift x c) = softmax x :=
  h

/-- Roadmap exemplar: a rounding implementation refines a target format
relation. -/
theorem rounding_refines_format_relation {α : Type*}
    (round : ℝ → α) (rel : ℝ → α → Prop)
    (h : RoundingRefines round rel) :
    ∀ x, rel x (round x) :=
  h

end RelSem

namespace MXVec

variable {K m : Nat}

/-- Roadmap exemplar: the block-factored MX dot product refines the
fully decoded real dot product. -/
theorem blockDot_refines_decoded_dot (a b : MXVec K m) :
    MX.MXVec.dotBlocked a b = MX.MXVec.dotDecoded a b :=
  MX.MXVec.dotBlocked_eq_dotDecoded a b

end MXVec

namespace E2M1

/-- E2M1 specialization of `rounding_refines_format_relation` for
round-to-nearest-even. -/
theorem rounding_refines_format_relation (x : ℝ) :
    MX.E2M1.IsRoundedToNearestEven x (MX.E2M1.roundRNE x) :=
  MX.E2M1.roundRNE_isRNE x

end E2M1

namespace ProbAffine

/-- A finite probability distribution, kept deliberately small so
stochastic rounding examples do not need the full probability library
yet. -/
structure FinDist (α : Type*) [Fintype α] where
  prob : α → ℝ
  nonneg : ∀ a, 0 ≤ prob a
  mass_one : (∑ a, prob a) = 1

/-- Finite-support expectation over a `FinDist`. -/
noncomputable def expectation {α : Type*} [Fintype α]
    (d : FinDist α) (f : α → ℝ) : ℝ :=
  ∑ a, d.prob a * f a

/-- A variance budget for independent zero-mean error terms. -/
def VarianceBound {K : Nat} (variance : Fin K → ℝ) (bound : ℝ) : Prop :=
  (∀ i, 0 ≤ variance i) ∧ (∑ i : Fin K, variance i) ≤ bound

/-- Roadmap exemplar: a stochastic sum is bounded by the chosen
sum-of-variances budget. -/
theorem stochastic_sum_variance_bound {K : Nat}
    (variance : Fin K → ℝ)
    (h_nonneg : ∀ i, 0 ≤ variance i) :
    VarianceBound variance (∑ i : Fin K, variance i) :=
  ⟨h_nonneg, le_rfl⟩

/-- The summed variance budget is nonnegative when each independent term
has nonnegative variance. -/
theorem stochastic_sum_variance_nonneg {K : Nat}
    (variance : Fin K → ℝ)
    (h_nonneg : ∀ i, 0 ≤ variance i) :
    0 ≤ ∑ i : Fin K, variance i :=
  Finset.sum_nonneg fun i _ => h_nonneg i

/-- A scalar quantizer is unbiased when its decoded finite-support
expectation equals the source real. -/
def UnbiasedScalarQuantizer {Q : Type*} [Fintype Q]
    (dist : ℝ → FinDist Q) (decode : Q → ℝ) : Prop :=
  ∀ x, expectation (dist x) decode = x

/-- Roadmap exemplar: if every scalar quantizer in a dot-product input
is unbiased, then the weighted dot against deterministic weights is
unbiased. -/
theorem quantized_dot_unbiased {K : Nat} {Q : Type*} [Fintype Q]
    (dist : Fin K → ℝ → FinDist Q)
    (decode : Q → ℝ)
    (x y : Fin K → ℝ)
    (h_unbiased : ∀ i, expectation (dist i (x i)) decode = x i) :
    (∑ i : Fin K, y i * expectation (dist i (x i)) decode) =
      ∑ i : Fin K, y i * x i := by
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [h_unbiased i]

end ProbAffine

end Roadmap
end MX
