# LeanFloats

Lean 4 / Mathlib formalizations of two binary floating-point families:

- **IEEEFloat** — strict IEEE 754-2019 binary interchange formats (`binary16`, `binary32`, `binary64`, plus `bfloat16` for ML), parameterized over exponent width `eb` and trailing-mantissa width `mb`.
- **MX** — the Open Compute Project Microscaling specification v1.0 (block-scaled low-precision floats; element format `E2M1` (FP4), scale format `E8M0`, block size `K = 32`).

Both libraries share the structural concept (sign + biased exponent + trailing mantissa) but differ in implementation: `IEEEFloat` reserves the all-ones exponent for NaN/∞, while MX has no NaN or ∞ at the element level (block-level NaN is carried by the scale).

## Status

No `sorry`, no `axiom`, no `admit`. `lake build` passes against `mathlib v4.28.0` on Lean `v4.28.0`.

This is currently a single-author research codebase. The IEEEFloat layer ships:

- The type, predicates (`isNaN` / `isInf` / `isFinite` / `isZero` / `isSubnormal` / `isNormal`), and format constants (`bias`, `maxExp`, `minNormalExp`, `minSubnormalExp`).
- `finiteValue : F → ℝ` and `toReal : F → Option ℝ` bridging to Mathlib's `ℝ`.
- Round-to-nearest-even spec (`IsRoundedToNearestEven`) and a classical `roundToNearest` whose existence is proved via `Finset.exists_min_image`.
- Correctly-rounded `add` / `sub` / `mul` / `div` contracts (`IsCorrectlyRounded*`), and explicit (still `noncomputable`) implementations satisfying them.
- Half-ULP error bounds for in-range RN results, plus per-op wrappers and `unitRoundoff` / `machineEpsilon`.
- Bit-pattern interchange (`toBits` / `fromBits`) with round-trip and injectivity proofs, verified against the four standard formats' canonical hex encodings.
- ULP / `nextFinite` / `prevFinite`, monotonicity, parity alternation, encoding-adjacency (no real value strictly between adjacent encodings), and a positive-finite trichotomy.
- Cross-format conversion (§5.4.2), integer ↔ float conversions, all five §4.3 rounding-mode specs, comparison predicates (§5.6), `minimum` / `maximum` / `minimumNumber` / `maximumNumber` (§5.3.1), `abs` / `copySign` / `fpclass`.

The MX layer ships `E2M1` / `E8M0` / `MXBlock`, decode/encode/round, ops + backend, comparison, kernel-style operations (dot, reduction, GEMM, RMSNorm, softmax, transformer block), and tree-dependence reasoning.

For per-module summaries see the doc-comments in [`IEEEFloat.lean`](IEEEFloat.lean) and [`MX.lean`](MX.lean).

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
