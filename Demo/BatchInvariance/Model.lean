import Demo.BatchInvariance.Backend

/-! # The toy LLM

A minimal transformer-style model: token embedding → one
transformer block (RMSNorm → linear → softmax → linear) →
unembedding linear projection to vocab logits.

Each batch position is a single token (sequence length `T = 1`).
The batch-invariance question — does swapping in a different batch
of inputs change what position `i` sees? — is meaningful at this
size: the unembedding is a real GEMM-style layer whose batched
implementation could in principle introduce cross-batch coupling
(via a hostile `Backend` instance).  Multi-token sequences,
multi-head attention, and multi-layer stacks are downstream
extensions; their batch-invariance proofs compose from this one.

## Forward routing

  *  `forwardRow M token` = `unembedding.apply ∘ block.applyRow ∘
                              embedTable.get` — pure spec, no
                              `Backend`.
  *  `forwardBatch M tokens b v` — routed through
     `Backend.layerApplyBatch` at the unembedding step.  The
     hidden-state tensor (post-block, pre-unembed) is built
     row-by-row from the per-token spec, then passed to the
     backend.

A `BatchInvariant` instance witnesses that the two agree:
`forwardBatch M tokens b v = forwardRow M (tokens b) v`.

## Why route only the unembedding through `Backend`

The embedding is a pure lookup (no arithmetic, hence no
implementation freedom for a hostile backend to exploit).  The
transformer block uses row-by-row pure functions internally
(`Block.applyRow`); its batched form is by *definition*
`fun X b => applyRow (X.get b)` — no separate batched
implementation exists.  Only the unembedding is a real GEMM that
a hostile silicon-style backend could implement with cross-batch
coupling.

In a more elaborate toy LLM (multi-head attention, multi-layer
stack), every linear-projection step would route through
`Backend.layerApplyBatch`; this single-block, single-layer model
is the minimum that exhibits the structure. -/

namespace Demo.BatchInvariance.Model
open Demo.BatchInvariance MX

variable {α : Type} {V K m : Nat}

/-- The toy LLM.

      *  `embedTable`  — vocab-sized table of embedding rows.
      *  `block`       — a transformer block whose output is the
                          (re-quantized) hidden state, ready for the
                          unembedding GEMM.
      *  `unembedding` — final linear projection to vocab logits. -/
structure ToyLLM (α : Type) (V K m : Nat) where
  embedTable  : MXMatrix V K m
  block       : TransformerBlock.Block (MXVec K m) K m K m
  unembedding : Forward.Layer α K m V

namespace ToyLLM

/-- Hidden state of a single token after embedding + transformer
    block.  This is the input to the unembedding layer. -/
def hiddenRow (M : ToyLLM α V K m) (token : Fin V) : MXVec K m :=
  M.block.applyRow (M.embedTable.get token)

/-- Per-token forward: hidden → unembed → logit at vocab index. -/
def forwardRow (M : ToyLLM α V K m) (token : Fin V) : Fin V → α :=
  fun v => M.unembedding.apply (M.hiddenRow token) v

/-- The hidden-state tensor at the unembedding's input, built
    row-by-row from `hiddenRow`. -/
def hiddenBatch (M : ToyLLM α V K m) {B : Nat}
    (tokens : Fin B → Fin V) : MXMatrix B K m :=
  List.Vector.ofFn (fun b => M.hiddenRow (tokens b))

/-- Batched forward.  The unembedding step routes through
    `Backend.layerApplyBatch`, so a hostile backend could in
    principle return a different value than the row reference. -/
def forwardBatch [Backend α] (M : ToyLLM α V K m) {B : Nat}
    (tokens : Fin B → Fin V) : Fin B → Fin V → α :=
  fun b v => Backend.layerApplyBatch M.unembedding (M.hiddenBatch tokens) b v

/-! ## Forward-pass batch invariance

For any batch-invariant backend, the batched forward at position
`b` agrees bitwise with running the singleton `tokens b`. -/

/-- **Forward-pass batch invariance (toy LLM).**
    `forwardBatch tokens b v = forwardRow (tokens b) v` for any
    batch-invariant backend, any vocabulary index `v`, and any
    batch position `b`. -/
theorem forwardBatch_eq_forwardRow [Backend α] [BatchInvariant α]
    (M : ToyLLM α V K m) {B : Nat}
    (tokens : Fin B → Fin V) (b : Fin B) (v : Fin V) :
    M.forwardBatch tokens b v = M.forwardRow (tokens b) v := by
  unfold forwardBatch forwardRow hiddenBatch
  rw [BatchInvariant.layer_batch_eq_apply, List.Vector.get_ofFn]

/-! ## Permutation invariance

Reordering the batch reorders the output likewise.  Falls out of
forward-pass batch invariance as a two-line corollary. -/

/-- **Permutation invariance (forward).**  Reordering the input
    tokens by a permutation `σ` reorders the output rows by `σ`.
    Concretely: `forwardBatch (tokens ∘ σ) b v
                  = forwardBatch tokens (σ b) v`. -/
theorem forwardBatch_permute [Backend α] [BatchInvariant α]
    (M : ToyLLM α V K m) {B : Nat}
    (tokens : Fin B → Fin V) (σ : Equiv.Perm (Fin B))
    (b : Fin B) (v : Fin V) :
    M.forwardBatch (tokens ∘ σ) b v = M.forwardBatch tokens (σ b) v := by
  rw [forwardBatch_eq_forwardRow, forwardBatch_eq_forwardRow]
  rfl

end ToyLLM

end Demo.BatchInvariance.Model
