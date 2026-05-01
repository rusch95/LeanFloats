import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring
import MX.E2M1
import MX.Block

/-! # Sign-level operations on E2M1 and MXBlock

Operations that touch only the sign bit (and per-element sign for blocks):

  *  `abs`       — clear sign bit.
  *  `neg`       — flip sign bit.  (Already in `MX.E2M1`; re-exported here
                    via the `Neg` instance.)
  *  `copySign`  — copy the sign of one operand onto another.
  *  `fpclass`   — unified class predicate.

All total, computable, constructor-level — no rounding, no `ℝ`
arithmetic.  Mirrors `IEEEFloat.Ops`, simplified by the absence of
NaN / Inf at the *element* level (E2M1 has neither).  The block-level
NaN tag (carried on the E8M0 scale) is preserved by these ops since
they touch only element data.
-/

namespace MX

namespace E2M1

/-! ## `abs` -/

/-- Absolute value: clear the sign bit. -/
def abs (x : E2M1) : E2M1 := { x with s := false }

@[simp] theorem abs_def (x : E2M1) : abs x = ⟨false, x.e, x.m⟩ := rfl

@[simp] theorem abs_pos (e : Fin 4) (m : Fin 2) :
    abs ⟨false, e, m⟩ = ⟨false, e, m⟩ := rfl

@[simp] theorem abs_neg_pat (e : Fin 4) (m : Fin 2) :
    abs ⟨true, e, m⟩ = ⟨false, e, m⟩ := rfl

theorem abs_idem (x : E2M1) : abs (abs x) = abs x := by
  cases x; rfl

/-- `abs` clears the sign bit. -/
theorem s_abs (x : E2M1) : (abs x).s = false := rfl

/-- `abs (-x) = abs x`. -/
theorem abs_neg_eq (x : E2M1) : abs (-x) = abs x := by
  cases x; rfl

/-- The positive-sign reading is nonnegative.  Brute-force over the
    8 (e, m) patterns. -/
private theorem toReal_pos_nonneg (e : Fin 4) (m : Fin 2) :
    0 ≤ toReal ⟨false, e, m⟩ := by
  fin_cases e <;> fin_cases m <;> (unfold toReal bias; norm_num)

/-- Sign-flip on the bit pattern negates `toReal`. -/
private theorem toReal_pat_neg (e : Fin 4) (m : Fin 2) :
    toReal ⟨true, e, m⟩ = -toReal ⟨false, e, m⟩ := by
  fin_cases e <;> fin_cases m <;> (unfold toReal bias; norm_num)

/-- `abs` and the real-valued absolute value agree.  Every E2M1 has
    `|toReal| ∈ {0, 0.5, 1, 1.5, 2, 3, 4, 6}`. -/
theorem toReal_abs (x : E2M1) : (abs x).toReal = |x.toReal| := by
  rcases x with ⟨s, e, m⟩
  show toReal ⟨false, e, m⟩ = |toReal ⟨s, e, m⟩|
  rcases s with _ | _
  · rw [abs_of_nonneg (toReal_pos_nonneg e m)]
  · rw [toReal_pat_neg, abs_neg, abs_of_nonneg (toReal_pos_nonneg e m)]

/-! ## `copySign` -/

/-- Copy the sign bit of `y` onto `x`. -/
def copySign (x y : E2M1) : E2M1 := { x with s := y.s }

@[simp] theorem copySign_def (x y : E2M1) :
    copySign x y = ⟨y.s, x.e, x.m⟩ := rfl

theorem copySign_self (x : E2M1) : copySign x x = x := by
  cases x; rfl

theorem copySign_abs (x y : E2M1) : copySign (abs x) y = copySign x y := rfl

/-- `copySign x y` has the same sign as `y`. -/
theorem s_copySign (x y : E2M1) : (copySign x y).s = y.s := rfl

/-- `copySign` preserves the magnitude bits. -/
theorem e_copySign (x y : E2M1) : (copySign x y).e = x.e := rfl

theorem m_copySign (x y : E2M1) : (copySign x y).m = x.m := rfl

/-! ## Floating-point class

E2M1 has six classes (no NaN, no Inf):

  *  `posZero` / `negZero`
  *  `posSubnormal` / `negSubnormal`  (the ±0.5 patterns)
  *  `posNormal` / `negNormal`
-/

/-- The IEEE 754 §5.7.2 floating-point classes, restricted to the six
    that exist in E2M1. -/
inductive FpClass
  | posZero
  | negZero
  | posSubnormal
  | negSubnormal
  | posNormal
  | negNormal
  deriving DecidableEq, Repr

/-- Classify an E2M1 value. -/
def fpclass (x : E2M1) : FpClass :=
  match x.s, x.e.val, x.m.val with
  | false, 0, 0 => .posZero
  | true,  0, 0 => .negZero
  | false, 0, _ => .posSubnormal
  | true,  0, _ => .negSubnormal
  | false, _, _ => .posNormal
  | true,  _, _ => .negNormal

@[simp] theorem fpclass_pos_zero : fpclass ⟨false, 0, 0⟩ = .posZero := rfl
@[simp] theorem fpclass_neg_zero : fpclass ⟨true, 0, 0⟩ = .negZero := rfl
@[simp] theorem fpclass_pos_half : fpclass ⟨false, 0, 1⟩ = .posSubnormal := rfl
@[simp] theorem fpclass_neg_half : fpclass ⟨true, 0, 1⟩ = .negSubnormal := rfl

end E2M1

namespace MXBlock

variable {K : Nat}

/-! ## Block-level sign operations

Block sign ops touch every element's sign bit.  The block scale is
unaffected, so a NaN-tagged block stays NaN-tagged.  Useful when
implementing per-block "negation" or "absolute value" passes that
appear in some kernels (e.g., layer-norm gradient flows). -/

/-- Block-level absolute value: clear every element's sign bit.  The
    scale (and its NaN status) is unchanged. -/
def abs (b : MXBlock K) : MXBlock K :=
  { b with elements := b.elements.map E2M1.abs }

/-- Block-level negation: flip every element's sign bit. -/
def neg (b : MXBlock K) : MXBlock K :=
  { b with elements := b.elements.map E2M1.neg }

instance : Neg (MXBlock K) := ⟨neg⟩

@[simp] theorem abs_scale (b : MXBlock K) : (abs b).scale = b.scale := rfl
@[simp] theorem neg_scale (b : MXBlock K) : (neg b).scale = b.scale := rfl

/-- Block-abs preserves NaN-tagging. -/
@[simp] theorem isNaN_abs (b : MXBlock K) : (abs b).isNaN = b.isNaN := rfl
@[simp] theorem isNaN_neg (b : MXBlock K) : (neg b).isNaN = b.isNaN := rfl

/-- Block-abs is element-wise abs. -/
@[simp] theorem abs_elements_get (b : MXBlock K) (i : Fin K) :
    (abs b).elements.get i = E2M1.abs (b.elements.get i) := by
  simp [abs, List.Vector.get_map]

/-- Block-neg is element-wise neg. -/
@[simp] theorem neg_elements_get (b : MXBlock K) (i : Fin K) :
    (neg b).elements.get i = -(b.elements.get i) := by
  simp [neg, List.Vector.get_map, E2M1.neg]

/-- Block-abs is idempotent. -/
theorem abs_abs (b : MXBlock K) : abs (abs b) = abs b := by
  rcases b with ⟨s, elts⟩
  simp [abs]
  apply List.Vector.ext
  intro i
  rw [List.Vector.get_map, List.Vector.get_map]
  exact E2M1.abs_idem _

/-- Block-neg is involutive. -/
theorem neg_neg (b : MXBlock K) : -(-b) = b := by
  show neg (neg b) = b
  rcases b with ⟨s, elts⟩
  simp only [neg]
  congr 1
  apply List.Vector.ext
  intro i
  rw [List.Vector.get_map, List.Vector.get_map]
  exact E2M1.neg_neg _

end MXBlock

end MX
