import MX.Block

/-! # MXBlock decoding to real values

The decoded value of element `i` in a block:

  *  If `block.scale.isNaN`: `none` (entire block tagged as NaN).
  *  Otherwise: `some (scaleReal · elem[i].toReal)`.

This module provides element-wise decoding plus the headline result
that the decoded vector commutes with the block scale: scaling all
elements at decode time is equivalent to baking the scale into each
element's individual real value.
-/

namespace MX

namespace MXBlock

variable {K : Nat}

/-- Decode a single element of the block. -/
noncomputable def decodeAt (b : MXBlock K) (i : Fin K) : Option ℝ :=
  match b.scale.toReal with
  | none      => none
  | some s    => some (s * (b.elements.get i).toReal)

/-- The decoded value of element `i` is `scale * elem.toReal` when
    the scale is finite, and `none` (NaN-tagged) when the scale is NaN. -/
theorem decodeAt_eq (b : MXBlock K) (i : Fin K) :
    b.decodeAt i = if b.scale.isNaN
      then none
      else some (b.scale.toRealOrZero * (b.elements.get i).toReal) := by
  unfold decodeAt E8M0.toReal E8M0.toRealOrZero E8M0.isNaN
  by_cases h : b.scale.raw = E8M0.nanRaw
  · simp [h]
  · simp [h]

/-! ## All-NaN propagation -/

theorem decodeAt_nan (b : MXBlock K) (h : b.isNaN = true) (i : Fin K) :
    b.decodeAt i = none := by
  unfold decodeAt
  simp [isNaN, E8M0.isNaN] at h
  unfold E8M0.toReal
  simp [h]

theorem decodeAt_finite (b : MXBlock K) (h : b.isNaN = false) (i : Fin K) :
    b.decodeAt i = some (b.scale.toRealOrZero * (b.elements.get i).toReal) := by
  rw [decodeAt_eq, if_neg]
  simp [isNaN] at h
  exact Bool.eq_false_iff.mp h

/-! ## Scale commutativity

For non-NaN blocks, scaling at decode time agrees with scaling each
element's real value. -/

theorem decode_scale_factor (b : MXBlock K) (i : Fin K)
    (h : b.isNaN = false) :
    ∃ s : ℝ, b.decodeAt i = some (s * (b.elements.get i).toReal) := by
  refine ⟨b.scale.toRealOrZero, ?_⟩
  exact decodeAt_finite b h i

/-! ## Vectorized decode

`decode b : List.Vector (Option ℝ) K` produces an option for each
position.  All-`some` exactly when the scale isn't NaN. -/

/-- Decode a block to a vector of `Option ℝ`. -/
noncomputable def decode (b : MXBlock K) : List.Vector (Option ℝ) K :=
  List.Vector.ofFn fun i => b.decodeAt i

@[simp] theorem decode_get (b : MXBlock K) (i : Fin K) :
    (decode b).get i = b.decodeAt i := by
  simp [decode, List.Vector.get_ofFn]

/-- All elements decode to `none` when the block is NaN-tagged. -/
theorem decode_nan (b : MXBlock K) (h : b.isNaN = true) :
    ∀ i, (decode b).get i = none := fun i => by
  rw [decode_get]; exact decodeAt_nan b h i

/-- All elements decode to `some _` when the block isn't NaN-tagged. -/
theorem decode_finite (b : MXBlock K) (h : b.isNaN = false) :
    ∀ i, (decode b).get i =
        some (b.scale.toRealOrZero * (b.elements.get i).toReal) := fun i => by
  rw [decode_get]; exact decodeAt_finite b h i

end MXBlock

end MX
