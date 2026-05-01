import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import MX.Dot

/-! # Reduction trees over MX block dot products

Property 4 (`MX/Dot.lean`) factors an MX-vector dot product into an
outer sum over `m = K_total / 32` block products plus a per-block
inner sum where the scales factor out.  The outer sum has `m` terms
to combine into one — and the *order* in which they are combined
matters as soon as the underlying additive structure is non-
associative or non-commutative.

This module formalizes "fix the outer reduction order → deterministic
output," parameterized by an abstract `ReductionTree`.

## What is a `ReductionTree`?

A `ReductionTree α m` is a function `(Fin m → α) → α`.  Concrete kernel
implementations of GEMM realize this as a binary tree of `+` operations
(sequential left-fold, pairwise tree, Kahan-summed fold, etc.); the
function form abstracts over the choice.

The two regimes that matter:

  *  **Over `[AddCommMonoid α]` (e.g., `ℝ`).**  Any "valid" tree (one
     that sums its inputs) returns the same value.  Tree shape is
     irrelevant.  This is why MX-GEMM over `ℝ` is trivially batch-
     invariant — you don't even need to fix the tree.

  *  **Over a non-commutative / non-associative additive type (fp
     accumulators).**  Different tree shapes give different rounded
     sums.  Once the tree is *fixed* (the kernel's reduction order is
     determined only by `m`, not by tile size or batch), evaluation is
     a pure function of `(tree, inputs)` and we recover bitwise
     determinism.

Property 5 in this file is the second observation in formal form: a
fixed tree is a pure function.  Over ℝ it's rfl; the value lives in
the *statement*, which lays the groundwork for the batch-invariance
theorem in `MX.GEMM`.

## Why not an inductive `Shape : Nat → Type`?

We initially considered `inductive Shape | leaf : Shape 1 | node : Shape l → Shape r → Shape (l+r)`.
That formulation is more concrete (you can write a left-fold or a
pairwise tree as a value of `Shape m`), but the dependent `l+r` index
generates substantial casting overhead in proofs that pivot on
`Shape`-extensionality.  The functional encoding `(Fin m → α) → α`
captures the same content (a deterministic m-ary reduction) without
the dependent-type tax, and it's the right level of abstraction for
the batch-invariance argument: we only ever ask "does the output
depend on `(a, b)` alone, given a fixed reduction?", and the answer
is structural, not shape-dependent.
-/

namespace MX

/-- A reduction tree over `m` positions: a function that combines an
    `m`-indexed family of values into a single output.  Concrete
    kernels realize this as a specific tree of `+` operations. -/
abbrev ReductionTree (α : Type*) (m : Nat) : Type _ := (Fin m → α) → α

namespace ReductionTree

variable {α : Type*} {m : Nat}

/-- A reduction tree is "a sum over a commutative monoid" if its output
    matches `Finset.sum` for every input.  Over `[AddCommMonoid α]` all
    valid trees are extensionally equal; over a non-commutative
    additive type this predicate may fail. -/
def IsSumOver [AddCommMonoid α] (t : ReductionTree α m) : Prop :=
  ∀ f : Fin m → α, t f = ∑ i : Fin m, f i

/-- **Determinism.**  A reduction tree is a pure function: equal inputs
    give equal outputs.  Over `ℝ` the proof is rfl; the operative
    content is what the *statement* says — once the tree is fixed (no
    secret dependence on tile size, batch dimension, or other context),
    its output is determined by `(tree, inputs)` alone. -/
theorem deterministic (t : ReductionTree α m) {f g : Fin m → α} (h : f = g) :
    t f = t g := by rw [h]

/-- **Pointwise determinism.**  If two index-functions agree pointwise,
    the tree's outputs match.  Used downstream when arguing the dot
    product depends only on each block, since "block agrees pointwise"
    is the natural form after Property 4. -/
theorem deterministic_pointwise (t : ReductionTree α m) {f g : Fin m → α}
    (h : ∀ i, f i = g i) : t f = t g :=
  deterministic t (funext h)

/-! ## Over commutative monoids, all valid trees agree -/

/-- **Tree shape is irrelevant over a commutative monoid.**  Two valid
    sum-trees produce the same answer on every input.  Specialized to
    `ℝ` this says: an MX dot product over reals is independent of the
    outer reduction order, so batch invariance is automatic without
    any extra constraint on the kernel.  The constraint becomes
    binding only when we move to fp accumulators (Lean's `Float`,
    `IEEEFloat`, etc., which are not commutative monoids under their
    rounded `+`). -/
theorem eq_of_isSumOver [AddCommMonoid α]
    (t1 t2 : ReductionTree α m)
    (h1 : t1.IsSumOver) (h2 : t2.IsSumOver) (f : Fin m → α) :
    t1 f = t2 f := by rw [h1 f, h2 f]

/-! ## A canonical tree: `Finset.sum`

Over `[AddCommMonoid α]`, `Finset.sum` is itself a `ReductionTree` and
trivially satisfies `IsSumOver`.  Concrete fp kernels implementing a
left-fold, pairwise reduction, etc., are different `ReductionTree`s
that happen to be equal *over ℝ* (or any commutative monoid) but
differ under fp rounding. -/

/-- The canonical sum-as-tree.  Definitionally a `ReductionTree`. -/
def sumTree [AddCommMonoid α] : ReductionTree α m := fun f => ∑ i : Fin m, f i

theorem sumTree_isSumOver [AddCommMonoid α] :
    (sumTree : ReductionTree α m).IsSumOver := fun _ => rfl

end ReductionTree

/-! ## Application to MX dot product -/

namespace MXVec

variable {K m : Nat}

/-- The MX block-factored dot product, evaluated through an explicit
    outer reduction tree.  The inner per-block sum stays as a `Finset`
    sum over `Fin K`; only the outer sum across `m` blocks is routed
    through `t`. -/
noncomputable def dotBlockedTree
    (t : ReductionTree ℝ m) (a b : MXVec K m) : ℝ :=
  t (fun j => MXBlock.blockDot (a.get j) (b.get j))

/-- A tree that "sums over reals" evaluates `dotBlockedTree` to the
    canonical `dotBlocked`. -/
theorem dotBlockedTree_eq_dotBlocked
    (t : ReductionTree ℝ m) (h : t.IsSumOver) (a b : MXVec K m) :
    dotBlockedTree t a b = dotBlocked a b := by
  unfold dotBlockedTree dotBlocked
  exact h _

/-- The canonical `dotBlocked` is `dotBlockedTree` with the
    `sumTree` reducer. -/
theorem dotBlocked_eq_dotBlockedTree_sumTree (a b : MXVec K m) :
    dotBlocked a b = dotBlockedTree ReductionTree.sumTree a b := rfl

/-! ## Property 5 — outer-reduction-tree determinism

The headline result of this module: once `t` is fixed, `dotBlockedTree
t a b` is a pure function of `(a, b)` — equivalently, of the per-block
data only.  No tile size, batch dimension, or split-K factor enters.

Over `ℝ` this is structurally trivial; the *contribution* of stating
it is making the dependence on `t` explicit, so a downstream batch-
invariance proof for MX-GEMM can be parameterized by the kernel's
choice of `t`. -/

/-- **Property 5: determinism via fixed reduction tree.**  Two MX
    vector pairs that agree block-by-block have the same dot product
    under any fixed reduction tree.

    Used in Property 7 (`MX.GEMM`) to peel off the batch dimension:
    the kernel computes output row `b` by `dotBlockedTree t (A.row b) Bᵀ.col n`,
    so any property of `(A.row b, Bᵀ.col n)` determines the output. -/
theorem dotBlockedTree_congr
    (t : ReductionTree ℝ m) (a a' b b' : MXVec K m)
    (ha : ∀ j, a.get j = a'.get j) (hb : ∀ j, b.get j = b'.get j) :
    dotBlockedTree t a b = dotBlockedTree t a' b' := by
  unfold dotBlockedTree
  apply ReductionTree.deterministic_pointwise
  intro j
  rw [ha j, hb j]

/-- **Property 5 over ℝ: tree shape is irrelevant.**  Two valid sum
    trees produce the same `dotBlockedTree` value over reals.  Implies
    that a switch between left-fold, pairwise, etc., does not change
    the result — over reals.  In fp, this fails, and the kernel must
    *commit* to a tree to remain deterministic. -/
theorem dotBlockedTree_tree_irrelevant_over_reals
    (t1 t2 : ReductionTree ℝ m) (h1 : t1.IsSumOver) (h2 : t2.IsSumOver)
    (a b : MXVec K m) :
    dotBlockedTree t1 a b = dotBlockedTree t2 a b := by
  unfold dotBlockedTree
  exact ReductionTree.eq_of_isSumOver t1 t2 h1 h2 _

/-! ## Property 5 lifted to a generic accumulator

The ℝ-valued definitions above are the "no rounding" specification.
Real MXFP4 kernels accumulate the m block products in a finite-
precision accumulator (FP32 in most current hardware, BF16 in some).
We abstract the accumulator as an arbitrary type `Acc` together with
a per-block rounding function `round : ℝ → Acc`; the outer reduction
tree `t : ReductionTree Acc m` then operates on `Acc`.

The batch-invariance proof carries over verbatim because it depends
only on "fixed tree is a function of its inputs," which is type-
generic.  Tree-irrelevance over reals
(`dotBlockedTree_tree_irrelevant_over_reals`) does *not* lift — a
counterexample exists for `Acc := IEEEFloat 8 23` with the standard
nearest-even rounding, and that counterexample is exactly the
phenomenon the Thinking Machines blog post on batch nondeterminism
diagnoses.  Stating it as the contrapositive of `eq_of_isSumOver`
over fp is a future module. -/

/-- The MX dot product evaluated through an arbitrary outer
    accumulator.  Each block's `ℝ`-valued `blockDot` is rounded into
    `Acc` via `round`, then the m rounded values are combined by `t`.

    Specializing `Acc := ℝ` and `round := id` recovers
    `dotBlockedTree`; see `dotBlockedTreeAcc_id_eq_dotBlockedTree`. -/
noncomputable def dotBlockedTreeAcc {Acc : Type*}
    (round : ℝ → Acc) (t : ReductionTree Acc m)
    (a b : MXVec K m) : Acc :=
  t (fun j => round (MXBlock.blockDot (a.get j) (b.get j)))

/-- `Acc := ℝ`, `round := id` recovers the ℝ-valued `dotBlockedTree`. -/
theorem dotBlockedTreeAcc_id_eq_dotBlockedTree
    (t : ReductionTree ℝ m) (a b : MXVec K m) :
    dotBlockedTreeAcc id t a b = dotBlockedTree t a b := rfl

/-- **Property 5 over an arbitrary accumulator.**  For any `Acc`, any
    `round : ℝ → Acc`, and any fixed reduction tree `t : ReductionTree
    Acc m`, two MX-vector pairs that agree block-by-block produce the
    same accumulator value.  The proof is the same as the ℝ case
    (`deterministic_pointwise`) because `ReductionTree` is type-
    generic — no algebraic property of `+` is used. -/
theorem dotBlockedTreeAcc_congr {Acc : Type*}
    (round : ℝ → Acc) (t : ReductionTree Acc m)
    (a a' b b' : MXVec K m)
    (ha : ∀ j, a.get j = a'.get j) (hb : ∀ j, b.get j = b'.get j) :
    dotBlockedTreeAcc round t a b = dotBlockedTreeAcc round t a' b' := by
  unfold dotBlockedTreeAcc
  apply ReductionTree.deterministic_pointwise
  intro j
  rw [ha j, hb j]

end MXVec
end MX
