import LowFloat.FP4.E2M1

/-! # Compatibility re-export for MXFP4 E2M1

The canonical scalar type now lives at `LowFloat.FP4.E2M1`.  This
module preserves the historical `MX.E2M1` API as reducible aliases to
the canonical definitions.
-/

namespace MX

/-- Historical MX namespace alias for the shared FP4 E2M1 scalar. -/
abbrev E2M1 : Type := LowFloat.FP4.E2M1

namespace E2M1

abbrev bias : Int := LowFloat.FP4.E2M1.bias
noncomputable abbrev toReal : E2M1 → ℝ := LowFloat.FP4.E2M1.toReal

noncomputable abbrev maxValue : ℝ := LowFloat.FP4.E2M1.maxValue
noncomputable abbrev minPositive : ℝ := LowFloat.FP4.E2M1.minPositive

abbrev isZero : E2M1 → Bool := LowFloat.FP4.E2M1.isZero
abbrev isSubnormal : E2M1 → Bool := LowFloat.FP4.E2M1.isSubnormal
abbrev isNormal : E2M1 → Bool := LowFloat.FP4.E2M1.isNormal
abbrev isPositive : E2M1 → Bool := LowFloat.FP4.E2M1.isPositive

abbrev neg : E2M1 → E2M1 := LowFloat.FP4.E2M1.neg

abbrev toBits : E2M1 → BitVec 4 := LowFloat.FP4.E2M1.toBits
abbrev fromBits : BitVec 4 → E2M1 := LowFloat.FP4.E2M1.fromBits

export LowFloat.FP4.E2M1
  (toReal_pos_zero toReal_neg_zero toReal_pos_half toReal_neg_half
   toReal_pos_one toReal_pos_three_halves toReal_pos_two toReal_pos_three
   toReal_pos_four toReal_pos_six toReal_neg_six
   neg_eq neg_neg toReal_neg)

end E2M1

end MX
