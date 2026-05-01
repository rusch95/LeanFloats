import MX.Encode

/-! # Multi-block / matrix-level MX quantization

A single `MXBlock K` holds `K` elements with one shared `E8M0` scale.
Real workloads quantize *vectors of length K·m* by partitioning into
`m` blocks, and *matrices of shape (B × K·m)* by quantizing each row
independently.  This module formalizes the multi-block layer on top
of the per-block `Encode` API.

## Layout

We work with **pre-split** vectors and matrices throughout: a "row"
of length K·m is represented as `List.Vector (List.Vector ℝ K) m`
rather than `List.Vector ℝ (K*m)`.  The split is orthogonal to the
batch-invariance properties we want to prove and would only obscure
the per-row reasoning.

  * `MXVec K m`      = `List.Vector (MXBlock K) m`            — encoded row.
  * `RowReal K m`    = `List.Vector (List.Vector ℝ K) m`      — pre-split row.
  * `MXMatrix B K m` = `List.Vector (MXVec K m) B`            — encoded matrix.
  * `MatReal B K m`  = `List.Vector (RowReal K m) B`          — pre-split matrix.

## Property 2 — row independence

`(encodeMatrix M).get b = encodeRow (M.get b)`.  The MX-encoded form
of row `b` depends only on row `b`'s real values; rows other than `b`
do not enter the computation.  This is the load-bearing setup lemma
for batch invariance: when we later show the GEMM kernel produces
output row `b` from MX-encoded row `b` of the activations, this
theorem lets us peel off the batch dimension entirely.
-/

namespace MX

/-- An MX-encoded row: `m` blocks, each of size `K`. -/
abbrev MXVec (K m : Nat) : Type := List.Vector (MXBlock K) m

/-- A pre-split real-valued row: `m` chunks of `K` reals. -/
abbrev RowReal (K m : Nat) : Type := List.Vector (List.Vector ℝ K) m

/-- An MX-encoded matrix: `B` rows, each an `MXVec K m`. -/
abbrev MXMatrix (B K m : Nat) : Type := List.Vector (MXVec K m) B

/-- A pre-split real-valued matrix: `B` rows, each a `RowReal K m`. -/
abbrev MatReal (B K m : Nat) : Type := List.Vector (RowReal K m) B

namespace MXVec

variable {K m B : Nat}

/-- Encode a pre-split row block-by-block.  Each block uses
    `MXBlock.encode` (which currently picks `chooseScale`); see
    `encodeRowOptimal` below for the optimal-scale variant. -/
noncomputable def encodeRow (r : RowReal K m) : MXVec K m :=
  r.map MXBlock.encode

@[simp] theorem encodeRow_get (r : RowReal K m) (j : Fin m) :
    (encodeRow r).get j = MXBlock.encode (r.get j) := by
  simp [encodeRow, List.Vector.get_map]

/-- Encode all rows of a matrix independently. -/
noncomputable def encodeMatrix (M : MatReal B K m) : MXMatrix B K m :=
  M.map encodeRow

@[simp] theorem encodeMatrix_get (M : MatReal B K m) (b : Fin B) :
    (encodeMatrix M).get b = encodeRow (M.get b) := by
  simp [encodeMatrix, List.Vector.get_map]

/-! ## Property 2 — row independence

Stated two ways:

  *  `row_independence`: the encoded row at index `b` equals the
     encoding of row `b` in isolation.
  *  `encodeMatrix_congr_row`: two matrices that agree at row `b`
     produce the same encoded row at `b` — formalizing "rows other
     than `b` don't matter".

Both follow from the element-wise structure of `encodeMatrix`.  The
content of these theorems is not the proof difficulty (it is a one-
liner) but the *statement*: it pins down that MX quantization has no
hidden cross-row dependencies, which a per-tensor scaling scheme
would not satisfy. -/

/-- **Row independence.**  The b-th row of `encodeMatrix M` is the
    encoding of `M.get b` — no contribution from other rows. -/
theorem row_independence (M : MatReal B K m) (b : Fin B) :
    (encodeMatrix M).get b = encodeRow (M.get b) :=
  encodeMatrix_get M b

/-- **Row independence (congruence form).**  If two matrices agree at
    row `b`, their encoded matrices also agree at row `b`.  This is the
    form you cite when arguing batch invariance: adding, removing, or
    perturbing rows other than `b` cannot change the encoded row `b`. -/
theorem encodeMatrix_congr_row
    (M M' : MatReal B K m) (b : Fin B) (h : M.get b = M'.get b) :
    (encodeMatrix M).get b = (encodeMatrix M').get b := by
  rw [row_independence, row_independence, h]

/-- **Row independence at the block level.**  Each individual block
    of the encoded matrix depends only on the corresponding block of
    real values, not on the surrounding row or matrix.  Combines
    `row_independence` with `encodeRow_get`. -/
theorem encodeMatrix_get_block
    (M : MatReal B K m) (b : Fin B) (j : Fin m) :
    ((encodeMatrix M).get b).get j = MXBlock.encode ((M.get b).get j) := by
  rw [row_independence, encodeRow_get]

/-! ## Optimal-scale variants

Mirroring `MXBlock.encodeOptimal` for callers who want the tightest
per-block error.  Requires a uniform bound on every element of every
block. -/

/-- The boundedness predicate: every element of every block in the
    row is within the maximum representable range of MXFP4. -/
def RowBounded (r : RowReal K m) : Prop :=
  ∀ (j : Fin m) (i : Fin K), |((r.get j).get i)| ≤ 6 * (2 : ℝ) ^ (127 : ℤ)

/-- Encode a row using `encodeOptimal` per block.  Requires a per-block
    bound so the optimal scale is well-defined. -/
noncomputable def encodeRowOptimal (r : RowReal K m) (h : RowBounded r) :
    MXVec K m :=
  List.Vector.ofFn fun j => MXBlock.encodeOptimal (r.get j) (h j)

@[simp] theorem encodeRowOptimal_get
    (r : RowReal K m) (h : RowBounded r) (j : Fin m) :
    (encodeRowOptimal r h).get j = MXBlock.encodeOptimal (r.get j) (h j) := by
  simp [encodeRowOptimal, List.Vector.get_ofFn]

/-- Row-independence holds for the optimal-scale encoder too: the
    encoded row at block `j` depends only on `r.get j` (and the local
    bound at that block). -/
theorem encodeRowOptimal_get_eq_of_block_eq
    (r r' : RowReal K m) (h : RowBounded r) (h' : RowBounded r')
    (j : Fin m) (heq : r.get j = r'.get j) :
    (encodeRowOptimal r h).get j = (encodeRowOptimal r' h').get j := by
  rw [encodeRowOptimal_get, encodeRowOptimal_get]
  -- `encodeOptimal` is dependent (its boundedness proof references
  -- the block), so the substitution `r.get j ↦ r'.get j` only
  -- typechecks via `congr` / dependent-rewrite machinery.
  congr 1

end MXVec
end MX
