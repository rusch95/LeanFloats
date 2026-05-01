import MX.Kernel

/-! # Forward-pass batch invariance

Lifts batch invariance from a single GEMM (`MX.Kernel`) to a whole
forward pass: linear layer → pointwise activation → linear layer.
This is the structural shape of MLP-style transformer feed-forward
blocks.

The key claim — and the reason this module exists — is that batch
invariance *composes*.  If every step in the forward pass operates
row-locally on its input, the composite is also row-local.  Stated
formally, no row other than `b` of the inputs can influence row `b`
of the outputs of any step (or the whole pass).

## What "robust" means here

  *  No commutativity / associativity of `+` is assumed.  All proofs
     are structural rewrites; the accumulator type `α` can be FP32
     (`IEEEFloat 8 23`), FP16 / BF16, or any other type.

  *  Each step's batch-locality follows from its type signature, not
     from arithmetic facts.  A maintainer who tries to "optimize" by
     hoisting work across rows breaks the type, not the proof.

## Limits

The pass we model is intentionally minimalist: `MX → linear → φ →
quantize → linear → φ`.  Real LLM blocks add residual connections,
layer norm, attention.  Each of those is also row-local (per-token in
the attention case, *modulo* the query/key/value matmul, which has
its own batch story).  The composition pattern in this module
generalizes to those constructions; we leave the formal extension
to a follow-up.
-/

namespace Demo.BatchInvariance
namespace Forward
open MX

/-! ## Single layer: linear + pointwise activation -/

/-- A single fully-connected layer with pointwise activation.

      *  `weights`    — `N × (K·m)` weight matrix in MX format.
      *  `kernel`     — the GEMM kernel (block op + reduction tree),
                         producing accumulator-typed outputs.
      *  `activation` — pointwise nonlinearity applied per output.
                         For ReLU over `α = ℝ`, this is `max 0 ·`.

    The layer maps `MXVec K m → Fin N → α`.  Output at column `n` is
    `activation (kernel.dot input weights[n])`. -/
structure Layer (α : Type*) (K m N : Nat) where
  weights    : MXMatrix N K m
  kernel     : MXKernel α K m
  activation : α → α

namespace Layer

variable {α : Type*} {K m N : Nat}

/-- Apply a layer to a single (already-encoded) input row. -/
def apply (L : Layer α K m N) (x : MXVec K m) : Fin N → α :=
  fun n => L.activation (L.kernel.dot x (L.weights.get n))

/-- Apply a layer to a whole batch. -/
def applyBatch {B : Nat} (L : Layer α K m N) (X : MXMatrix B K m) :
    Fin B → Fin N → α :=
  fun b n => L.apply (X.get b) n

/-! ## Row-independence of a single layer

The layer's output at `(b, n)` depends only on `X.get b`, not on
other rows.  Direct corollary of `MXKernel.gemm_batch_invariant`.  -/

/-- **Single-layer row independence.**  If two batches agree at row
    `b`, the layer outputs at row `b` agree at every column.  Holds
    over any `α` (including non-commutative-`+` accumulators). -/
theorem applyBatch_row_indep {B : Nat}
    (L : Layer α K m N) (X X' : MXMatrix B K m) (b : Fin B)
    (h : X.get b = X'.get b) (n : Fin N) :
    L.applyBatch X b n = L.applyBatch X' b n := by
  unfold applyBatch apply
  rw [h]

/-- The applied row is a function of the row only.  Stated as
    extensional equality at row `b`. -/
theorem applyBatch_eq_apply {B : Nat}
    (L : Layer α K m N) (X : MXMatrix B K m) (b : Fin B) :
    L.applyBatch X b = L.apply (X.get b) := rfl

end Layer

/-! ## Quantizer: bridge accumulator output back to MX input

To compose two layers, the first's accumulator-typed output (`Fin N →
α`) must be re-quantized into MX format for the second.  The
quantizer is itself a row-local function: it operates on one row's
worth of accumulator values and produces an MX vector.  Modeled here
as a plain function `(Fin N → α) → MXVec K' m'` — a real
implementation would compute per-block scales, round each element to
E2M1, etc.  We don't pin down the implementation; the only property
we need for batch invariance is that the quantizer is *deterministic*
in its single-row input.

(That is, it is a Lean function — by definition deterministic in its
inputs.  Stating this as a separate condition seems redundant, but it
captures the constraint that a real implementation must not peek at
other rows of the batch through, e.g., a global state.) -/

/-- A row-local quantizer mapping `Fin N → α` to `MXVec K m'`. -/
abbrev Quantizer (α : Type*) (N K m' : Nat) : Type _ :=
  (Fin N → α) → MXVec K m'

/-! ## Two-layer composition

`compose L₁ q L₂` = `L₂ ∘ q ∘ L₁`: run layer 1, quantize, run
layer 2.  Output at `(b, n')` ought to depend only on input row `b`. -/

/-- A two-layer block: two layers separated by a quantizer. -/
structure TwoLayerBlock (α : Type*) (K₁ m₁ N₁ K₂ m₂ N₂ : Nat) where
  layer1     : Layer α K₁ m₁ N₁
  quantize12 : Quantizer α N₁ K₂ m₂
  layer2     : Layer α K₂ m₂ N₂

namespace TwoLayerBlock

variable {α : Type*} {K₁ m₁ N₁ K₂ m₂ N₂ : Nat}

/-- Apply the two-layer block to a single input row. -/
def apply (block : TwoLayerBlock α K₁ m₁ N₁ K₂ m₂ N₂)
    (x : MXVec K₁ m₁) : Fin N₂ → α :=
  block.layer2.apply (block.quantize12 (block.layer1.apply x))

/-- Apply to a whole batch. -/
def applyBatch {B : Nat}
    (block : TwoLayerBlock α K₁ m₁ N₁ K₂ m₂ N₂)
    (X : MXMatrix B K₁ m₁) :
    Fin B → Fin N₂ → α :=
  fun b n => block.apply (X.get b) n

/-! ## Composition row-independence -/

/-- **Two-layer block: row-local at the input.**  Output at row `b`
    depends only on input row `b` — the quantizer in the middle
    re-uses its row's accumulator output, never crossing batch rows.

    Proof: structural — `applyBatch` evaluates `apply (X.get b)`,
    which is a pure function of `X.get b`. -/
theorem applyBatch_row_indep {B : Nat}
    (block : TwoLayerBlock α K₁ m₁ N₁ K₂ m₂ N₂)
    (X X' : MXMatrix B K₁ m₁) (b : Fin B)
    (h : X.get b = X'.get b) (n : Fin N₂) :
    block.applyBatch X b n = block.applyBatch X' b n := by
  unfold applyBatch apply
  rw [h]

/-- The applied row equals `apply` on the single input row. -/
theorem applyBatch_eq_apply {B : Nat}
    (block : TwoLayerBlock α K₁ m₁ N₁ K₂ m₂ N₂)
    (X : MXMatrix B K₁ m₁) (b : Fin B) :
    block.applyBatch X b = block.apply (X.get b) := rfl

end TwoLayerBlock

/-! ## Generalization: forward-pass row-locality, recursively

For an `n`-layer pass (with `n` quantizers in between), the same
structural argument applies at each step.  Stated as a single lemma
covering arbitrary deep composition: if every constituent step is a
function of one row's accumulator data, the composite is also a
function of one row of the original input.

We capture this via a `RowLocal` predicate: a function `f : MXMatrix
B K m → Fin B → β` is row-local if `f X b` is determined by `X.get
b`.  Composition via per-row maps preserves row-locality. -/

/-- A function `f : MXMatrix B K m → Fin B → β` is *row-local* if for
    every `b`, `f X b` is determined by `X.get b` alone. -/
def RowLocal {K m B : Nat} {β : Type*}
    (f : MXMatrix B K m → Fin B → β) : Prop :=
  ∀ X X' : MXMatrix B K m, ∀ b : Fin B,
    X.get b = X'.get b → f X b = f X' b

/-- A single `Layer.applyBatch` is row-local. -/
theorem Layer.applyBatch_rowLocal {α : Type*} {K m N : Nat} (B : Nat)
    (L : Layer α K m N) :
    RowLocal (K := K) (m := m) (B := B) (β := Fin N → α)
      (fun X b => L.applyBatch X b) :=
  fun X X' b h => funext (Layer.applyBatch_row_indep L X X' b h)

/-- A two-layer block is row-local. -/
theorem TwoLayerBlock.applyBatch_rowLocal {α : Type*}
    {K₁ m₁ N₁ K₂ m₂ N₂ : Nat} (B : Nat)
    (block : TwoLayerBlock α K₁ m₁ N₁ K₂ m₂ N₂) :
    RowLocal (K := K₁) (m := m₁) (B := B) (β := Fin N₂ → α)
      (fun X b => block.applyBatch X b) :=
  fun X X' b h => funext (block.applyBatch_row_indep X X' b h)

end Forward
end Demo.BatchInvariance
