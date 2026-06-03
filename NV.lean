import NV.E4M3
import NV.Block
import NV.Decode

/-! # NVFP4 — NVIDIA FP4 micro-block format

This library formalizes the core decoding semantics of NVFP4:

  * E2M1 FP4 elements, reused from `LowFloat.FP4.E2M1`.
  * One shared FP8 E4M3 scale per micro-block.
  * Standard micro-block size `K = 16`.
  * A second-level per-tensor FP32 scale, represented as a real
    parameter to decoding.

The decoded value at index `i` is

`tensorScale * block.scale * block.elements[i]`.

This is intentionally a first core layer: it does not yet include
quantizer selection of E4M3 scales, packed tensor layouts, or
kernel-level GEMM/RMSNorm/softmax theorems analogous to `MX`.
-/
