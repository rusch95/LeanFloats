# LeanFloats

Lean 4 / Mathlib formalizations of four low-precision floating-point families:

- **IEEEFloat** — strict IEEE 754-2019 binary interchange formats (`binary16`, `binary32`, `binary64`, plus `bfloat16` for ML), parameterized over exponent width `eb` and trailing-mantissa width `mb`.
- **LowFloat** — shared scalar low-precision formats used by current AI accelerators: FP4 `E2M1`, FP6 `E2M3` / `E3M2`, OCP FP8 `E4M3` / `E5M2` / `E8M0`, AMD CDNA3 FP8 FNUZ variants, NVIDIA PTX `UE4M3`, adjacent `S2F6` fixed-point, and TF32.
- **MX** — the Open Compute Project Microscaling specification v1.0 (block-scaled low-precision floats; element format `E2M1` (FP4), scale format `E8M0`, block size `K = 32`).
- **NV** — NVIDIA-style NVFP4 micro-blocks (element format `E2M1`, scale format `E4M3` FP8, block size `K = 16`, plus a per-tensor FP32 scale represented as a real-valued decode parameter).

The libraries share the structural concept (sign + biased exponent + trailing mantissa) but differ in implementation: `IEEEFloat` reserves the all-ones exponent for NaN/∞, `LowFloat` tracks vendor/OCP special-value conventions explicitly, MX has no NaN or ∞ at the element level (block-level NaN is carried by the scale), and NVFP4 uses E4M3 FP8 scales with no infinities and a NaN scale tag.

## Status

No `sorry`, no `axiom`, no `admit`. `lake build` passes against `mathlib v4.28.0` on Lean `v4.28.0`.

This is currently a single-author research codebase. The IEEEFloat layer ships:

- The type, predicates (`isNaN` / `isInf` / `isFinite` / `isZero` / `isSubnormal` / `isNormal`), and format constants (`bias`, `maxExp`, `minNormalExp`, `minSubnormalExp`).
- `finiteValue : F → ℝ` and `toReal : F → Option ℝ` bridging to Mathlib's `ℝ`.
- Round-to-nearest-even spec (`IsRoundedToNearestEven`) and a classical `roundToNearest` whose existence is proved via `Finset.exists_min_image`.
- Correctly-rounded `add` / `sub` / `mul` / `div` contracts (`IsCorrectlyRounded*`), and explicit (still `noncomputable`) implementations satisfying them.
- Half-ULP error bounds for in-range RN results, theorem-backed normal-result relative-error bounds, plus per-op wrappers and `unitRoundoff` / `machineEpsilon`.
- Bit-pattern interchange (`toBits` / `fromBits`) with round-trip and injectivity proofs, verified against the four standard formats' canonical hex encodings.
- ULP / `nextFinite` / `prevFinite`, monotonicity, parity alternation, encoding-adjacency (no real value strictly between adjacent encodings), and a positive-finite trichotomy.
- Cross-format conversion (§5.4.2), integer ↔ float conversions, all five §4.3 rounding-mode specs, comparison predicates (§5.6), `minimum` / `maximum` / `minimumNumber` / `maximumNumber` (§5.3.1), `abs` / `copySign` / `fpclass`.
- `IEEEFloat.FloatSpec` instances for `F32` / `F16` / `BF16` expose the rigorous normal-result arithmetic bounds; unconditional relative-error bounds are intentionally omitted because they are false at subnormal underflow.

The LowFloat layer ships scalar decode/bit-layout coverage for:

- FP4 `E2M1`, FP6 `E2M3` / `E3M2`, OCP FP8 `E4M3` / `E5M2`, and E8M0 scales.
- AMD CDNA3 / MI300 FP8 FNUZ `E4M3` / `E5M2`, where `0x80` is NaN and signed zero is absent.
- NVIDIA PTX alternate `UE4M3` and the adjacent `S2F6` fixed-point format so new Blackwell/PTX low-precision paths are visible.
- TF32 as the scalar `IEEEFloat 8 10` format.
- Generic E8M0-scaled block shells for MXFP4, MXFP6, and MXFP8 decode semantics; kernel behavior is intentionally left to downstream repos.

The MX layer ships `E2M1` / `E8M0` / `MXBlock`, decode/encode/round, ops + backend, comparison, kernel-style operations (dot, reduction, GEMM, RMSNorm, softmax, transformer block), and tree-dependence reasoning.

The NV layer ships `E4M3` / `NVBlock` / decode semantics for NVFP4 micro-blocks; quantizer selection and kernel-level theorems are intentionally left for follow-up.

For per-module summaries see the doc-comments in [`IEEEFloat.lean`](IEEEFloat.lean), [`LowFloat.lean`](LowFloat.lean), [`MX.lean`](MX.lean), and [`NV.lean`](NV.lean).

## Downstream

ML-side artifacts that consume these formal float and number-format
specs live in a sibling project,
[`LeanMachineLearning`](https://github.com/rusch95/LeanMachineLearning):

- `Tensors` — generic tensor abstractions over IEEE 754 binary
  formats.
- `BatchInvariance` — proof that a toy transformer-style LLM is
  bitwise batch-invariant on both forward and backward passes.

## Out of scope (deliberately)

- WGSL §15.7 relaxed semantics, LLVM `llvm.fmuladd` contraction, numpy-style alternative rounding modes — these belong layered on top of the IEEE contracts here.
- A bridge to Lean's host-native `Float` (a `bitcastFloat32 : Float → IEEEFloat 8 23` shim) — left for a follow-up `IEEEFloat.Host` module.
- Refined NaN sign + payload — IEEE leaves both implementation-defined; theorems at this layer must not depend on them. A bit-pattern-level refinement belongs in a separate module if needed.

## Build

```sh
lake exe cache get   # fetch Mathlib oleans
lake build
```

Toolchain pinned in [`lean-toolchain`](lean-toolchain); Mathlib version pinned in [`lakefile.lean`](lakefile.lean).

## License

Apache-2.0. See [LICENSE](LICENSE).
