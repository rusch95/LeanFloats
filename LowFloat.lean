import LowFloat.FP4.E2M1
import LowFloat.FP6.E2M3
import LowFloat.FP6.E3M2
import LowFloat.FP8.OCP.E4M3
import LowFloat.FP8.OCP.E5M2
import LowFloat.FP8.OCP.E8M0
import LowFloat.FP8.AMD.FNUZ
import LowFloat.PTX.UE4M3
import LowFloat.PTX.S2F6
import LowFloat.MX.ScaledBlock
import LowFloat.TF32

/-! # LowFloat — shared low-precision scalar formats

This root collects vendor-neutral and vendor-specific low-precision
number formats that are useful independently of any particular kernel:

  * FP4 `E2M1`.
  * FP6 `E2M3` and `E3M2`.
  * OCP FP8 `E4M3`, `E5M2`, and E8M0 scales.
  * AMD CDNA3 FP8 FNUZ `E4M3` / `E5M2`.
  * NVIDIA PTX alternate `UE4M3` and adjacent fixed-point `S2F6`.
  * TF32 as the `IEEEFloat 8 10` scalar format.
  * Generic E8M0-scaled MX block shells for FP4/FP6/FP8.

Kernel-level GEMM/reduction/RMSNorm/softmax behavior is intentionally
out of scope for this root.
-/
