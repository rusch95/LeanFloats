import Mathlib.Algebra.BigOperators.Ring.Finset
import MX.Quantize

/-! # Block-factored dot product

The MX format is structured around blocks of K elements sharing one
scale.  When two MX vectors are multiplied position-by-position and
summed (the dot product), the per-block scales factor cleanly out of
the inner sum:

  ` Σⱼ Σᵢ (sₐⱼ · aᵢⱼ.toReal) · (sᵦⱼ · bᵢⱼ.toReal) `
  ` = Σⱼ ( sₐⱼ · sᵦⱼ · Σᵢ aᵢⱼ.toReal · bᵢⱼ.toReal ) `

The right-hand side is a sum of *m* block products.  This is the
structural win that makes MX friendly to batch-invariant GEMM: the
outer reduction (the only one that fp-noncommutes against tile
reshaping) has size `m = K_total / 32` rather than `K_total`.

## Property 4 (this module)

`dotBlocked_eq_dotDecoded` (statement: `dotBlocked a b = dotDecoded a b`)
formalizes that the factored and unfactored forms compute the same real
number — i.e., the factorization is sound.  The block scales can be
hoisted out of the inner sum without changing the result.

This is over `ℝ`, where `+` is associative and commutative; the proof is
algebraic.  The downstream value of this module is that `dotBlocked` is
the form on which the `ReductionTree` machinery (Property 5) and the
batch-invariance theorem for MX-GEMM (Property 7) operate.

## NaN handling

We use `toRealOrZero` (NaN → 0) throughout, so a NaN-tagged block
contributes 0 to the dot.  The `Option ℝ`-flavored "strict" version
is recoverable from the `blockDot_nan_*` theorems below.
-/

namespace MX

namespace MXBlock

variable {K : Nat}

/-- The block-level dot product, with the two block scales pulled out
    of the inner sum.  Returns 0 if either block is NaN-tagged
    (because `toRealOrZero` is 0 for NaN scales). -/
noncomputable def blockDot (a b : MXBlock K) : ℝ :=
  a.scale.toRealOrZero * b.scale.toRealOrZero *
    ∑ i : Fin K, (a.elements.get i).toReal * (b.elements.get i).toReal

/-- A NaN-tagged left operand zeros the block dot. -/
theorem blockDot_nan_left (a b : MXBlock K) (h : a.isNaN = true) :
    blockDot a b = 0 := by
  have h_eq : a.scale.toRealOrZero = 0 := by
    unfold E8M0.toRealOrZero
    simp [isNaN, E8M0.isNaN] at h
    rw [if_pos h]
  unfold blockDot; rw [h_eq]; ring

/-- A NaN-tagged right operand zeros the block dot. -/
theorem blockDot_nan_right (a b : MXBlock K) (h : b.isNaN = true) :
    blockDot a b = 0 := by
  have h_eq : b.scale.toRealOrZero = 0 := by
    unfold E8M0.toRealOrZero
    simp [isNaN, E8M0.isNaN] at h
    rw [if_pos h]
  unfold blockDot; rw [h_eq]; ring

/-- For non-NaN blocks, `blockDot` equals the inner-sum-then-scale form
    used by hardware (multiply-accumulate the K element products in low
    precision, then multiply by the product of scales). -/
theorem blockDot_eq (a b : MXBlock K) :
    blockDot a b = a.scale.toRealOrZero * b.scale.toRealOrZero *
      ∑ i : Fin K, (a.elements.get i).toReal * (b.elements.get i).toReal := rfl

end MXBlock

namespace MXVec

variable {K m : Nat}

/-- The element-wise decoded value at position (j, i): the j-th block's
    scale times the i-th element's `toReal`.  Uses `toRealOrZero`, so a
    NaN block decodes to all zeros. -/
noncomputable def decodeAt (a : MXVec K m) (j : Fin m) (i : Fin K) : ℝ :=
  (a.get j).scale.toRealOrZero * ((a.get j).elements.get i).toReal

/-- Fully-decoded dot product: sum over all m·K positions of the
    elementwise products of decoded reals.  No factorization — every
    `(scale · element)` product is materialized. -/
noncomputable def dotDecoded (a b : MXVec K m) : ℝ :=
  ∑ j : Fin m, ∑ i : Fin K, decodeAt a j i * decodeAt b j i

/-- Block-factored dot product: outer sum over m blocks, with each
    block contributing `blockDot`.  The block scales are hoisted out of
    the inner K-wide sum. -/
noncomputable def dotBlocked (a b : MXVec K m) : ℝ :=
  ∑ j : Fin m, MXBlock.blockDot (a.get j) (b.get j)

/-! ## Property 4 — block-factoring is sound -/

/-- **Block-factored dot product equals fully-decoded dot product.**

    The two block scales factor out of each block's inner K-wide sum,
    leaving an outer sum over `m` block products.  Over `ℝ` this is a
    direct algebraic rearrangement (`Finset.mul_sum` per block, then
    `ring`).

    Significance: the outer reduction has size `m = K_total / 32`, not
    `K_total`.  When we move to a non-associative fp accumulator, the
    factorization shrinks the surface where reduction-order matters by
    32×.  Property 5 then pins down "fix the m-wide reduction tree and
    you have batch invariance". -/
theorem dotBlocked_eq_dotDecoded (a b : MXVec K m) :
    dotBlocked a b = dotDecoded a b := by
  unfold dotBlocked dotDecoded
  refine Finset.sum_congr rfl ?_
  intro j _
  unfold MXBlock.blockDot decodeAt
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

/-- The reverse direction, for callers who start with `dotDecoded`. -/
theorem dotDecoded_eq_dotBlocked (a b : MXVec K m) :
    dotDecoded a b = dotBlocked a b :=
  (dotBlocked_eq_dotDecoded a b).symm

/-! ## Block-locality of the dot product

A consequence of `dotBlocked` being a sum-of-block-products: the
contribution of block `j` to the dot is `blockDot (a.get j) (b.get j)`,
unaffected by other blocks.  This is what we'll use in Property 7
when arguing that perturbing other rows of a matmul cannot change a
given output. -/

/-- **Block-local dependence.**  If two MXVec pairs agree at every
    block index, their dot products are equal.  Trivial via congruence
    of finite sums; stated as a named lemma so downstream proofs can
    cite it without unfolding `dotBlocked`. -/
theorem dotBlocked_congr
    (a a' b b' : MXVec K m)
    (ha : ∀ j : Fin m, a.get j = a'.get j)
    (hb : ∀ j : Fin m, b.get j = b'.get j) :
    dotBlocked a b = dotBlocked a' b' := by
  unfold dotBlocked
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [ha j, hb j]

end MXVec
end MX
