import Mathlib.Data.Vector.Basic
import NV.Block

/-! # NVFP4 decoding

NVFP4 reconstructs each element as

`tensorScale * blockScale * elementValue`,

where `tensorScale` is the second-level FP32 scalar represented here
as a real number, `blockScale` is the shared E4M3 scale, and
`elementValue` is the E2M1 FP4 payload.
-/

namespace NV

namespace NVBlock

variable {K : Nat}

/-- Decode one NVFP4 element with a real-valued per-tensor scale. -/
noncomputable def decodeAt (tensorScale : ℝ) (b : NVBlock K) (i : Fin K) :
    Option ℝ :=
  match b.scale.toReal with
  | none => none
  | some s => some (tensorScale * s * (b.elements.get i).toReal)

/-- Element decode is tensor scale times E4M3 block scale times E2M1
    payload, unless the E4M3 scale is NaN. -/
theorem decodeAt_eq (tensorScale : ℝ) (b : NVBlock K) (i : Fin K) :
    b.decodeAt tensorScale i = if b.scale.isNaN
      then none
      else some (tensorScale * b.scale.toRealOrZero * (b.elements.get i).toReal) := by
  unfold decodeAt
  by_cases h : LowFloat.FP8.OCP.E4M3.isNaN b.scale
  · simp [LowFloat.FP8.OCP.E4M3.toReal, h]
  · simp [LowFloat.FP8.OCP.E4M3.toReal, LowFloat.FP8.OCP.E4M3.toRealOrZero, h]

theorem decodeAt_nan (tensorScale : ℝ) (b : NVBlock K)
    (h : b.isNaN = true) (i : Fin K) :
    b.decodeAt tensorScale i = none := by
  rw [decodeAt_eq]
  simp [isNaN] at h
  simp [h]

theorem decodeAt_finite (tensorScale : ℝ) (b : NVBlock K)
    (h : b.isNaN = false) (i : Fin K) :
    b.decodeAt tensorScale i =
      some (tensorScale * b.scale.toRealOrZero * (b.elements.get i).toReal) := by
  rw [decodeAt_eq]
  simp [isNaN] at h
  exact if_neg (Bool.eq_false_iff.mp h)

/-- Decode a block to a vector of optional real values. -/
noncomputable def decode (tensorScale : ℝ) (b : NVBlock K) :
    List.Vector (Option ℝ) K :=
  List.Vector.ofFn fun i => b.decodeAt tensorScale i

@[simp] theorem decode_get (tensorScale : ℝ) (b : NVBlock K) (i : Fin K) :
    (decode tensorScale b).get i = b.decodeAt tensorScale i := by
  simp [decode, List.Vector.get_ofFn]

/-- All elements decode to `none` when the block scale is NaN. -/
theorem decode_nan (tensorScale : ℝ) (b : NVBlock K) (h : b.isNaN = true) :
    ∀ i, (decode tensorScale b).get i = none := fun i => by
  rw [decode_get]
  exact decodeAt_nan tensorScale b h i

/-- All elements decode to concrete reals when the block scale is finite. -/
theorem decode_finite (tensorScale : ℝ) (b : NVBlock K) (h : b.isNaN = false) :
    ∀ i, (decode tensorScale b).get i =
      some (tensorScale * b.scale.toRealOrZero * (b.elements.get i).toReal) := fun i => by
  rw [decode_get]
  exact decodeAt_finite tensorScale b h i

end NVBlock

end NV
