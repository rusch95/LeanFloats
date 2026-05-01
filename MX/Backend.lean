import MX.Arith

/-! # Constructive arithmetic backend for E2M1 and E8M0

Mirrors `IEEEFloat.Backend`.  Provides explicit `add`, `sub`, `mul`,
`fma`, `div` for `E2M1` and `mul`, `inv` for `E8M0`, and proves each
satisfies its `IsCorrectlyRounded*` contract from `MX.Arith`.

The E2M1 backend is `noncomputable` because it dispatches through
`Real` arithmetic, then through `roundRNE` (which is itself
`noncomputable` — defined via `Classical.choose` over the 16 finite
representable values).  A *computable* backend that brute-forces the
nearest of the 16 patterns is straightforward but deferred.

The E8M0 backend is computable: the operations are pure exponent
arithmetic on raw bytes, no `Real` needed.
-/

namespace MX
namespace E2M1

/-! ## E2M1 arithmetic backends -/

/-- E2M1 addition: round the exact real sum to nearest-even,
    saturating at `±6`. -/
noncomputable def add (a b : E2M1) : E2M1 := roundRNE (a.toReal + b.toReal)

/-- E2M1 subtraction. -/
noncomputable def sub (a b : E2M1) : E2M1 := roundRNE (a.toReal - b.toReal)

/-- E2M1 multiplication. -/
noncomputable def mul (a b : E2M1) : E2M1 := roundRNE (a.toReal * b.toReal)

/-- E2M1 fused multiply-add (single rounding). -/
noncomputable def fma (a b c : E2M1) : E2M1 :=
  roundRNE (a.toReal * b.toReal + c.toReal)

/-- E2M1 division.  Detects zero divisor and saturates per the spec. -/
noncomputable def div (a b : E2M1) : E2M1 :=
  if b.isZero then
    if a.isZero then ⟨false, 0, 0⟩
    else ⟨decide (a.s ≠ b.s), 3, 1⟩
  else
    roundRNE (a.toReal / b.toReal)

/-! ## Correctness theorems -/

theorem add_isCorrectlyRounded (a b : E2M1) :
    IsCorrectlyRoundedAdd a b (add a b) :=
  ⟨roundRNE_isRNE _⟩

theorem sub_isCorrectlyRounded (a b : E2M1) :
    IsCorrectlyRoundedSub a b (sub a b) :=
  ⟨roundRNE_isRNE _⟩

theorem mul_isCorrectlyRounded (a b : E2M1) :
    IsCorrectlyRoundedMul a b (mul a b) :=
  ⟨roundRNE_isRNE _⟩

theorem fma_isCorrectlyRounded (a b c : E2M1) :
    IsCorrectlyRoundedFma a b c (fma a b c) :=
  ⟨roundRNE_isRNE _⟩

theorem div_isCorrectlyRounded (a b : E2M1) :
    IsCorrectlyRoundedDiv a b (div a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ha hb
    unfold div
    rw [if_pos hb, if_pos ha]
  · intro hb ha
    unfold div
    rw [if_pos hb, if_neg (by simp [ha] : ¬ a.isZero = true)]
  · intro hb
    unfold div
    rw [if_neg (by simp [hb] : ¬ b.isZero = true)]
    exact roundRNE_isRNE _

end E2M1

namespace E8M0

/-! ## E8M0 arithmetic backends

E8M0 multiplication is exact when in range — it's exponent addition.
The reciprocal is exponent reflection around the bias.  Both are
fully computable; no `Real` arithmetic is required. -/

/-- E8M0 multiplication: `2^a · 2^b = 2^(a+b)`, with saturation
    outside `[-127, 127]` and NaN propagation.

    Encoding: result raw is `a.raw + b.raw - 127` (since each raw is
    biased by 127, the bias must be subtracted once after summation).
    Saturating boundaries:
      *  `a.raw + b.raw < 127`  → underflow → raw 0   (= 2^(-127))
      *  `a.raw + b.raw ≥ 381` → overflow  → raw 254 (= 2^127) -/
def mul (a b : E8M0) : E8M0 :=
  if a.raw.val = 255 ∨ b.raw.val = 255 then
    nan
  else
    if h_lo : a.raw.val + b.raw.val < 127 then
      ⟨⟨0, by omega⟩⟩
    else if h_hi : a.raw.val + b.raw.val ≥ 381 then
      ⟨⟨254, by omega⟩⟩
    else
      ⟨⟨a.raw.val + b.raw.val - 127, by
        have ha := a.raw.isLt
        have hb := b.raw.isLt
        omega⟩⟩

/-- E8M0 reciprocal: `1 / 2^k = 2^(-k)`, encoded as `raw = 254 - a.raw`.
    NaN-propagating. -/
def inv (a : E8M0) : E8M0 :=
  if a.raw.val = 255 then nan
  else ⟨⟨254 - a.raw.val, by have := a.raw.isLt; omega⟩⟩

/-! ## Correctness -/

theorem mul_isCorrectlyMul (a b : E8M0) :
    IsCorrectlyMul a b (mul a b) := by
  refine ⟨?_, ?_⟩
  · intro h
    unfold mul
    have h_or : a.raw.val = 255 ∨ b.raw.val = 255 := by
      rcases h with h | h
      · left
        have : a.raw = nanRaw := by simp [isNaN] at h; exact h
        exact Fin.val_eq_of_eq this
      · right
        have : b.raw = nanRaw := by simp [isNaN] at h; exact h
        exact Fin.val_eq_of_eq this
    rw [if_pos h_or]
  · intro ha hb h_lo h_hi
    unfold mul
    have h_ne_a : a.raw.val ≠ 255 := fun he => by
      have : a.raw = nanRaw := Fin.ext he
      simp [isNaN, this] at ha
    have h_ne_b : b.raw.val ≠ 255 := fun he => by
      have : b.raw = nanRaw := Fin.ext he
      simp [isNaN, this] at hb
    rw [if_neg (by tauto : ¬ (a.raw.val = 255 ∨ b.raw.val = 255))]
    have h_lo' : ¬ a.raw.val + b.raw.val < 127 := by omega
    have h_hi' : ¬ a.raw.val + b.raw.val ≥ 381 := by omega
    rw [dif_neg h_lo', dif_neg h_hi']

theorem inv_isCorrectlyInv (a : E8M0) :
    IsCorrectlyInv a (inv a) := by
  refine ⟨?_, ?_⟩
  · intro h
    unfold inv
    have he : a.raw.val = 255 := by
      have : a.raw = nanRaw := by simp [isNaN] at h; exact h
      exact Fin.val_eq_of_eq this
    rw [if_pos he]
  · intro h
    unfold inv
    have h_ne : a.raw.val ≠ 255 := fun he => by
      have : a.raw = nanRaw := Fin.ext he
      simp [isNaN, this] at h
    rw [if_neg h_ne]

end E8M0
end MX
