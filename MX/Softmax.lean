import MX.GEMM_FP32

/-! # Softmax batch invariance

Softmax of a single row `x` of length `K · m` (numerically stable form):

  M       = max_i decoded(x_i)
  E_i     = exp(decoded(x_i) − M)
  S       = Σ_i E_i
  y_i     = E_i / S

Two reductions: a max-reduction for `M` and a sum-exp-reduction for
`S`.  The blog-post observation specializes to softmax with the
same shape: if the kernel commits two reduction trees (one for
each pass), both depending only on `m`, the per-row output is
bit-deterministic across batchings.

## Why this is "richer" than RMSNorm

RMSNorm is a single reduction (sum-of-squares).  Softmax is two
sequential reductions: the second pass depends on the first
pass's output (`M`).  But the *shape* of each reduction is
independently parameterized, and batch invariance follows the
same way: per-row output is determined by `(row, t_max, t_sumExp)`.

## What this module does NOT pin down

  *  The actual `max`, `exp`, and `/` over `Acc`.  Those are
     elementwise / scalar operations that don't affect the
     reduction structure.  We model them via abstract per-block
     functions (`perBlockMax`, `perBlockSumExp`) and an
     abstract `post : Acc → Acc → MXVec K m → β` final step.

  *  Numerical stability.  The "subtract M before exp" pattern is
     baked into the *type* of `perBlockSumExp` (it takes `M : Acc`
     as a parameter), but we don't prove anything about the
     resulting overflow behavior.
-/

namespace MX
namespace Softmax

variable {Acc β : Type*} {B K m : Nat}

/-- Softmax at the batch level, abstracting both reductions and the
    post-step.

    Parameters:
      *  `round`            — `ℝ → Acc` rounding (per block)
      *  `t_max`            — outer reduction tree for the max pass
      *  `t_sumExp`         — outer reduction tree for the sum-exp pass
      *  `perBlockMax`      — per-block max contribution
                              (e.g. `|s| · max_i |x_i|`)
      *  `perBlockSumExp`   — per-block sum-exp, parameterized by the
                              row's max value `M : Acc`
                              (e.g. `Σ_i exp(decoded(x_i) − M)`)
      *  `post`             — `(M : Acc) → (S : Acc) → (row : MXVec K m) → β`
                              packaging the elementwise division step
                              `y_i = exp(decoded(x_i) − M) / S`.

    The two reduction trees are independent — the kernel may use
    different shapes for the max and sum-exp passes, but each must
    depend only on `m`.

    All of `t_max`, `t_sumExp`, `perBlockMax`, `perBlockSumExp`, and
    `post` are inputs; the kernel realizes the standard formula by
    choosing concrete instantiations. -/
noncomputable def softmaxAcc
    (round : ℝ → Acc)
    (t_max : ReductionTree Acc m)
    (t_sumExp : ReductionTree Acc m)
    (perBlockMax : MXBlock K → ℝ)
    (perBlockSumExp : Acc → MXBlock K → ℝ)
    (post : Acc → Acc → MXVec K m → β)
    (X : MXMatrix B K m) (b : Fin B) : β :=
  let M := t_max (fun j => round (perBlockMax ((X.get b).get j)))
  let S := t_sumExp (fun j => round (perBlockSumExp M ((X.get b).get j)))
  post M S (X.get b)

/-- **Softmax batch invariance.**  For any fixed `t_max`, `t_sumExp`,
    per-block functions, and `post`, the softmax output at row `b`
    depends only on `X.get b`.  The two reduction trees, the
    rounding, and the post step are all parameters — the kernel
    must commit to specific choices, and once it does, the output
    is a function of `(t_max, t_sumExp, X.get b)` alone.

    Proof is `rw [h]` because the whole computation flows through
    `X.get b` and the tree parameters carry no implicit dependence
    on the batch dimension. -/
theorem softmaxAcc_batch_invariant
    (round : ℝ → Acc)
    (t_max : ReductionTree Acc m)
    (t_sumExp : ReductionTree Acc m)
    (perBlockMax : MXBlock K → ℝ)
    (perBlockSumExp : Acc → MXBlock K → ℝ)
    (post : Acc → Acc → MXVec K m → β)
    (X X' : MXMatrix B K m) (b : Fin B) (h : X.get b = X'.get b) :
    softmaxAcc round t_max t_sumExp perBlockMax perBlockSumExp post X b
      = softmaxAcc round t_max t_sumExp perBlockMax perBlockSumExp post X' b := by
  unfold softmaxAcc
  rw [h]

/-- Blockwise form: per-block agreement at row `b` suffices. -/
theorem softmaxAcc_batch_invariant_blockwise
    (round : ℝ → Acc)
    (t_max : ReductionTree Acc m)
    (t_sumExp : ReductionTree Acc m)
    (perBlockMax : MXBlock K → ℝ)
    (perBlockSumExp : Acc → MXBlock K → ℝ)
    (post : Acc → Acc → MXVec K m → β)
    (X X' : MXMatrix B K m) (b : Fin B)
    (h : ∀ j : Fin m, (X.get b).get j = (X'.get b).get j) :
    softmaxAcc round t_max t_sumExp perBlockMax perBlockSumExp post X b
      = softmaxAcc round t_max t_sumExp perBlockMax perBlockSumExp post X' b := by
  have hxx' : X.get b = X'.get b := List.Vector.ext h
  exact softmaxAcc_batch_invariant round t_max t_sumExp perBlockMax perBlockSumExp post
    X X' b hxx'

/-! ## Two-tree extension: orthogonal tree-irrelevance

For softmax, *each* reduction tree contributes its own batch-
nondeterminism risk.  Stating the negative result jointly: if
either `t_max` or `t_sumExp` is replaced by a different tree, the
output may change (over fp).  Stating the positive result: as
long as both are fixed in advance, the output is a function of
`(X.get b, t_max, t_sumExp)`. -/

/-- If only the `t_sumExp` tree changes (with `t_max` fixed), the
    output depends only on `(X.get b, t_max, t_sumExp)`.  Useful as
    a structural fact when reasoning about whether a kernel's
    optimization affects per-row outputs. -/
theorem softmaxAcc_t_sumExp_dependence
    (round : ℝ → Acc)
    (t_max : ReductionTree Acc m)
    (t_sumExp t_sumExp' : ReductionTree Acc m)
    (perBlockMax : MXBlock K → ℝ)
    (perBlockSumExp : Acc → MXBlock K → ℝ)
    (post : Acc → Acc → MXVec K m → β)
    (X : MXMatrix B K m) (b : Fin B)
    (h : t_sumExp = t_sumExp') :
    softmaxAcc round t_max t_sumExp perBlockMax perBlockSumExp post X b
      = softmaxAcc round t_max t_sumExp' perBlockMax perBlockSumExp post X b := by
  rw [h]

/-- Symmetric: the same statement for `t_max` with `t_sumExp` fixed. -/
theorem softmaxAcc_t_max_dependence
    (round : ℝ → Acc)
    (t_max t_max' : ReductionTree Acc m)
    (t_sumExp : ReductionTree Acc m)
    (perBlockMax : MXBlock K → ℝ)
    (perBlockSumExp : Acc → MXBlock K → ℝ)
    (post : Acc → Acc → MXVec K m → β)
    (X : MXMatrix B K m) (b : Fin B)
    (h : t_max = t_max') :
    softmaxAcc round t_max t_sumExp perBlockMax perBlockSumExp post X b
      = softmaxAcc round t_max' t_sumExp perBlockMax perBlockSumExp post X b := by
  rw [h]

end Softmax

/-! ## FP32 specialization -/

namespace Softmax

variable {β : Type*} {B K m : Nat}

/-- Softmax with an FP32 outer accumulator. -/
noncomputable def softmaxFP32
    (t_max : ReductionTree (IEEEFloat 8 23) m)
    (t_sumExp : ReductionTree (IEEEFloat 8 23) m)
    (perBlockMax : MXBlock K → ℝ)
    (perBlockSumExp : IEEEFloat 8 23 → MXBlock K → ℝ)
    (post : IEEEFloat 8 23 → IEEEFloat 8 23 → MXVec K m → β)
    (X : MXMatrix B K m) (b : Fin B) : β :=
  softmaxAcc roundFP32 t_max t_sumExp perBlockMax perBlockSumExp post X b

/-- **Bit-level batch invariance for FP32-accumulator MXFP4 softmax.**
    The third blog-post case study, formal. -/
theorem softmaxFP32_batch_invariant
    (t_max : ReductionTree (IEEEFloat 8 23) m)
    (t_sumExp : ReductionTree (IEEEFloat 8 23) m)
    (perBlockMax : MXBlock K → ℝ)
    (perBlockSumExp : IEEEFloat 8 23 → MXBlock K → ℝ)
    (post : IEEEFloat 8 23 → IEEEFloat 8 23 → MXVec K m → β)
    (X X' : MXMatrix B K m) (b : Fin B) (h : X.get b = X'.get b) :
    softmaxFP32 t_max t_sumExp perBlockMax perBlockSumExp post X b
      = softmaxFP32 t_max t_sumExp perBlockMax perBlockSumExp post X' b :=
  softmaxAcc_batch_invariant roundFP32 t_max t_sumExp perBlockMax perBlockSumExp post
    X X' b h

end Softmax

end MX
