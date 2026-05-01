import IEEEFloat.Backend
import IEEEFloat.RoundExistence
import MX.Kernel

/-! # Concrete MXFP4 kernel with FP32 accumulator

A concrete instantiation of `MXKernel` for MXFP4 (block size K = 32,
E2M1 elements, E8M0 scales) using `IEEEFloat 8 23` (FP32) as the
accumulator type — matching what real MXFP4 GPUs do.

## What this gets us

The abstract batch-invariance theorem in `MX.Kernel` is parameterized
over the accumulator type `α`.  Instantiating at `α = IEEEFloat 8 23`
(FP32) and committing to a specific reduction-tree shape (left-fold
via `IEEEFloat.add`) produces a fully concrete claim:

  ` MXFP4 GEMM with FP32 accumulator and a fixed reduction order is `
  ` batch-invariant. `

The proof is the same structural rewrite as the abstract version —
the genuine *content* is that the kernel's signature funnels A's
dependence through `A.get b`, and the type system makes that
explicit.  But the theorem statement is now about a concrete fp
arithmetic that hardware actually executes, not an abstract α.

## Decoders

E2M1 → FP32 is *exact*: every E2M1 value (`{0, ±0.5, ±1, ±1.5, ±2,
±3, ±4, ±6}`) has a finite FP32 encoding, so `roundToNearestEven`
introduces no rounding error here.  Similarly, E8M0 → FP32 is exact
for the standard scale range (`2^k`, `k ∈ [-127, 127]`), since FP32
covers powers of 2 from `2^(-149)` (subnormal) up to `2^127`.

We use `IEEEFloat.roundToNearestEven` rather than building bespoke
decoders, both for brevity and because the round-trip lemmas hold
trivially when the source format embeds in the target — no special-
case proofs needed downstream.

## Reduction tree

Concrete choice: **left-fold** (`((((x₀ + x₁) + x₂) + …) + x_{m-1})`).
This matches the simplest possible kernel implementation (a single
sequential accumulator).  Real GPUs use pairwise / tree-shaped
reductions for parallelism; switching is a matter of substituting a
different reduction-tree definition — the batch-invariance proof
goes through unchanged.

## Why noncomputable

`IEEEFloat.add`, `IEEEFloat.mul`, and `roundToNearestEven` are all
`noncomputable` in the upstream library — they dispatch through `ℝ`
arithmetic and `Classical.choose`.  Everything in this module
inherits that.  A computable backend (brute-forcing the nearest of
the finite Fp32 encodings) is straightforward but deferred.
-/

namespace MX
namespace MXFP4

/-- The accumulator type: IEEE 754 binary32 (FP32). -/
abbrev Fp32 : Type := IEEEFloat 8 23

/-- The standard MXFP4 block size: K = 32 elements per block. -/
abbrev K : Nat := 32

/-! ## Format width hypotheses for FP32

`IEEEFloat.add` and friends require `1 ≤ eb` and `1 ≤ mb` to
guarantee finite encodings exist.  Both hold trivially for FP32. -/

theorem heb : (1 : Nat) ≤ 8 := by omega
theorem hmb : (1 : Nat) ≤ 23 := by omega

/-! ## Decoders -/

/-- Decode an E2M1 element to FP32.  Exact: every E2M1 value is
    FP32-representable, so `roundToNearestEven` introduces no error. -/
noncomputable def decodeE2M1 (x : E2M1) : Fp32 :=
  IEEEFloat.roundToNearestEven heb hmb x.toReal

/-- Decode an E8M0 scale to FP32.  Exact for non-NaN scales (powers
    of 2 in `[2^(-127), 2^127]`, all FP32-representable).  NaN scales
    map to FP32 NaN so the rest of the kernel inherits NaN-tagging
    behavior. -/
noncomputable def decodeScale (a : E8M0) : Fp32 :=
  match a.toReal with
  | some r => IEEEFloat.roundToNearestEven heb hmb r
  | none   => .nan

/-! ## FP32 arithmetic helpers -/

/-- FP32 addition. -/
noncomputable def fp32Add (x y : Fp32) : Fp32 := IEEEFloat.add heb hmb x y

/-- FP32 multiplication. -/
noncomputable def fp32Mul (x y : Fp32) : Fp32 := IEEEFloat.mul heb hmb x y

/-- FP32 zero (positive). -/
def fp32Zero : Fp32 := .finite false ⟨0, by omega⟩ ⟨0, by omega⟩

/-! ## Left-fold reduction tree

Reduces an `m`-indexed family of FP32 values via sequential
left-association:
  `((((f 0 + f 1) + f 2) + …) + f (m-1))`.

Since FP32 `+` is non-associative, this commits to a specific
reduction order — switching to a different order (pairwise tree,
Kahan summation, etc.) gives a different rounded result, but the
batch-invariance theorem holds for any *fixed* choice. -/

/-- Auxiliary: left-fold over `Fin n` accumulating into `acc`.
    Iterates `i = 0, 1, …, n-1`. -/
noncomputable def foldlAux : (n : Nat) → (Fin n → Fp32) → Fp32 → Fp32
  | 0,     _, acc => acc
  | n + 1, f, acc =>
      foldlAux n (fun i => f i.castSucc) (fp32Add acc (f ⟨n, Nat.lt_succ_self n⟩))

/-- The left-fold reduction tree, starting from `+0`. -/
noncomputable def reduceLeftFold (m : Nat) : (Fin m → Fp32) → Fp32 :=
  fun f => foldlAux m f fp32Zero

/-! ## Block dot product

For each block-pair (a, b) of MXFP4 blocks:

  1. Per-element products, each in FP32: `decodeE2M1(a[i]) ⊗ decodeE2M1(b[i])`.
  2. Sum the K=32 products via the left-fold reduction tree.
  3. Multiply by the FP32 product of the two block scales.

This is the OCP MX block-dot operation as a real GPU implements it,
modulo our specific (left-fold) reduction-tree choice. -/

/-- The 32-element inner sum, left-folded in FP32. -/
noncomputable def innerSum (a b : MXBlock K) : Fp32 :=
  reduceLeftFold K (fun i => fp32Mul (decodeE2M1 (a.elements.get i))
                                      (decodeE2M1 (b.elements.get i)))

/-- The block dot product: scaled inner sum.  Returns FP32 NaN if
    either block is NaN-tagged (since `decodeScale` produces NaN). -/
noncomputable def blockOp (a b : MXBlock K) : Fp32 :=
  fp32Mul (fp32Mul (decodeScale a.scale) (decodeScale b.scale)) (innerSum a b)

/-! ## The concrete MXFP4 kernel -/

/-- The MXFP4 GEMM kernel with FP32 accumulator and left-fold outer
    reduction.  Concrete instantiation of `MXKernel`. -/
noncomputable def mxfp4Kernel (m : Nat) : MXKernel Fp32 K m where
  blockOp    := blockOp
  reduceTree := reduceLeftFold m

/-! ## Concrete batch invariance

The headline theorem in concrete form: an MXFP4 GEMM with FP32
accumulator and the specific left-fold reduction order produces an
output at row `b` that depends only on row `b` of `A`.

The proof is `MXKernel.gemm_batch_invariant` applied to the concrete
kernel.  The structural argument over abstract `α` carries through
unchanged — that's the whole point of the abstraction. -/

/-- **Concrete MXFP4 batch invariance.**  For an MXFP4 GEMM computing
    in FP32 via the specified left-fold reduction:

      `∀ A A' Wt b n, A.get b = A'.get b →
            (mxfp4Kernel m).gemm A Wt b n = (mxfp4Kernel m).gemm A' Wt b n`

    Concrete in three senses simultaneously: K = 32 (the OCP MXFP4
    block size), the accumulator is FP32 (`IEEEFloat 8 23`), and the
    outer reduction tree is left-fold via `IEEEFloat.add`.  Changing
    any of these requires re-instantiating, but the theorem statement
    keeps the same shape. -/
theorem mxfp4_gemm_batch_invariant {m B N : Nat}
    (A A' : MXMatrix B K m) (Wt : MXMatrix N K m)
    (b : Fin B) (n : Fin N) (h : A.get b = A'.get b) :
    (mxfp4Kernel m).gemm A Wt b n = (mxfp4Kernel m).gemm A' Wt b n :=
  MXKernel.gemm_batch_invariant (mxfp4Kernel m) A A' Wt b n h

/-- **Blockwise hypothesis form.**  Even weaker precondition: the two
    matrices need only agree at every block index of row `b`. -/
theorem mxfp4_gemm_batch_invariant_blockwise {m B N : Nat}
    (A A' : MXMatrix B K m) (Wt : MXMatrix N K m)
    (b : Fin B) (n : Fin N)
    (h : ∀ j : Fin m, (A.get b).get j = (A'.get b).get j) :
    (mxfp4Kernel m).gemm A Wt b n = (mxfp4Kernel m).gemm A' Wt b n :=
  MXKernel.gemm_batch_invariant_blockwise (mxfp4Kernel m) A A' Wt b n h

/-- **Encode-then-GEMM batch invariance.**  Starting from real-valued
    input matrices, encoding to MXFP4 and running the FP32-accumulator
    GEMM preserves row-locality.  Composes Property 2 (row-independence
    of MX quantization) with `mxfp4_gemm_batch_invariant`. -/
theorem mxfp4_encode_then_gemm_batch_invariant {m B N : Nat}
    (A A' : MatReal B K m) (Wt : MXMatrix N K m)
    (b : Fin B) (n : Fin N) (h : A.get b = A'.get b) :
    (mxfp4Kernel m).gemm (MXVec.encodeMatrix A) Wt b n =
      (mxfp4Kernel m).gemm (MXVec.encodeMatrix A') Wt b n :=
  MXKernel.encode_then_gemm_batch_invariant (mxfp4Kernel m) A A' Wt b n h

end MXFP4
end MX
