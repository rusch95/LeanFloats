import IEEEFloat.Arith
import IEEEFloat.Bits

/-! # Standard IEEE 754 binary interchange formats

Aliases for the four most-used widths, plus their concrete numerical
properties.  Each is a one-liner over `IEEEFloat`; the format-specific
constants (`bias`, `maxExp`, ULP thresholds) all derive from `(eb, mb)`
automatically — but we *verify* the derivation here to catch any
off-by-one in the underlying definitions.

  | alias       | bits | eb | mb | bias | role            |
  |-------------|------|----|----|------|-----------------|
  | `Binary16`  |  16  |  5 | 10 |   15 | f16 / IEEE half |
  | `Binary32`  |  32  |  8 | 23 |  127 | f32             |
  | `Binary64`  |  64  | 11 | 52 | 1023 | f64             |
  | `BFloat16`  |  16  |  8 |  7 |  127 | brain-float     |

`BFloat16` is not strictly an IEEE 754 interchange format — it shares
f32's exponent range with a truncated 7-bit mantissa.  Included here
because the rest of the library handles it uniformly.

For each format we land:
  *  `bias_eq`, `maxExp_eq`, `minNormalExp_eq`, `minSubnormalExp_eq` —
     verified concrete values for the integer constants.
  *  `zero` / `negZero` / `one` / `negOne` / canonical encodings.
  *  `*_toReal` — verified real values for those encodings.
  *  `toBits_*` — verified IEEE 754 hex bit patterns.

These act as both documentation and a sanity gate: if anyone perturbs
the underlying `bias` / `finiteValue` / `toBits` definitions in a way
that breaks the four real interchange formats, the build fails here.
-/

namespace IEEEFloat

/-- IEEE 754 binary16 (half precision). -/
abbrev Binary16 : Type := IEEEFloat 5 10

/-- IEEE 754 binary32 (single precision). -/
abbrev Binary32 : Type := IEEEFloat 8 23

/-- IEEE 754 binary64 (double precision). -/
abbrev Binary64 : Type := IEEEFloat 11 52

/-- bfloat16 (Google brain-float).  f32-range, 7-bit trailing mantissa. -/
abbrev BFloat16 : Type := IEEEFloat 8 7

/-! ## Binary16 (IEEE 754 half precision)

  *  16 total bits — 1 sign, 5 exp, 10 mantissa
  *  bias = 15, range ≈ 6×10⁻⁵ to 6×10⁴
  *  used in graphics, ML inference -/

namespace Binary16

theorem bias_eq            : (bias 5 : Int)            =   15 := by decide
theorem maxExp_eq          : (maxExp 5 : Int)          =   15 := by decide
theorem minNormalExp_eq    : (minNormalExp 5 : Int)    =  -14 := by decide
theorem minSubnormalExp_eq : (minSubnormalExp 5 10 : Int) = -24 := by decide

/-- +0. -/
def zero : Binary16 := .finite false ⟨0, by decide⟩ ⟨0, by decide⟩
/-- −0. -/
def negZero : Binary16 := .finite true ⟨0, by decide⟩ ⟨0, by decide⟩
/-- +1.0. -/
def one : Binary16 := .finite false ⟨15, by decide⟩ ⟨0, by decide⟩
/-- −1.0. -/
def negOne : Binary16 := .finite true ⟨15, by decide⟩ ⟨0, by decide⟩
/-- The smallest positive subnormal: `2⁻²⁴`. -/
def smallestPosSubnormal : Binary16 :=
  .finite false ⟨0, by decide⟩ ⟨1, by decide⟩
/-- The largest finite value: `(2 − 2⁻¹⁰) · 2¹⁵`. -/
def maxFiniteEnc : Binary16 :=
  .finite false ⟨2 ^ 5 - 1 - 1, by decide⟩ ⟨2 ^ 10 - 1, by decide⟩

theorem zero_toReal      : zero.toRealOrZero      =  0 := by
  unfold zero toRealOrZero finiteValue; simp
theorem negZero_toReal   : negZero.toRealOrZero   =  0 := by
  unfold negZero toRealOrZero finiteValue; simp
theorem one_toReal       : one.toRealOrZero       =  1 := by
  unfold one toRealOrZero finiteValue; simp [bias]
theorem negOne_toReal    : negOne.toRealOrZero    = -1 := by
  unfold negOne toRealOrZero finiteValue; simp [bias]

theorem maxFinite_eq :
    maxFinite 5 10 = (2 - (2:ℝ) ^ (-(10:Int))) * (2:ℝ) ^ (15:Int) := by
  unfold maxFinite; norm_num [maxExp, bias]
theorem minPosSubnormal_eq :
    minPosSubnormal 5 10 = (2:ℝ) ^ (-(24:Int)) := by
  unfold minPosSubnormal; norm_num [minSubnormalExp, minNormalExp, bias]
theorem topUlp_eq :
    topUlp 5 10 = (2:ℝ) ^ ((15:Int) - 10) := by
  unfold topUlp; norm_num [maxExp, bias]

theorem toBits_zero    : toBits zero    = 0x0000#16 := by decide
theorem toBits_negZero : toBits negZero = 0x8000#16 := by decide
theorem toBits_one     : toBits one     = 0x3C00#16 := by decide
theorem toBits_negOne  : toBits negOne  = 0xBC00#16 := by decide
theorem toBits_smallestPosSubnormal :
    toBits smallestPosSubnormal = 0x0001#16 := by decide
theorem toBits_maxFiniteEnc : toBits maxFiniteEnc = 0x7BFF#16 := by decide
theorem toBits_posInf  : toBits ((.inf false) : Binary16) = 0x7C00#16 := by decide
theorem toBits_negInf  : toBits ((.inf true)  : Binary16) = 0xFC00#16 := by decide
theorem toBits_nan     : toBits ((.nan)       : Binary16) = 0x7E00#16 := by decide

end Binary16

/-! ## Binary32 (IEEE 754 single precision)

  *  32 total bits — 1 sign, 8 exp, 23 mantissa
  *  bias = 127, range ≈ 1.4×10⁻⁴⁵ to 3.4×10³⁸
  *  the workhorse format for general numerics -/

namespace Binary32

theorem bias_eq            : (bias 8 : Int)            =  127 := by decide
theorem maxExp_eq          : (maxExp 8 : Int)          =  127 := by decide
theorem minNormalExp_eq    : (minNormalExp 8 : Int)    = -126 := by decide
theorem minSubnormalExp_eq : (minSubnormalExp 8 23 : Int) = -149 := by decide

/-- +0. -/
def zero : Binary32 := .finite false ⟨0, by decide⟩ ⟨0, by decide⟩
/-- −0. -/
def negZero : Binary32 := .finite true ⟨0, by decide⟩ ⟨0, by decide⟩
/-- +1.0. -/
def one : Binary32 := .finite false ⟨127, by decide⟩ ⟨0, by decide⟩
/-- −1.0. -/
def negOne : Binary32 := .finite true ⟨127, by decide⟩ ⟨0, by decide⟩
/-- The smallest positive subnormal: `2⁻¹⁴⁹`. -/
def smallestPosSubnormal : Binary32 :=
  .finite false ⟨0, by decide⟩ ⟨1, by decide⟩
/-- The largest finite value: `(2 − 2⁻²³) · 2¹²⁷`. -/
def maxFiniteEnc : Binary32 :=
  .finite false ⟨2 ^ 8 - 1 - 1, by decide⟩ ⟨2 ^ 23 - 1, by decide⟩

theorem zero_toReal    : zero.toRealOrZero    =  0 := by
  unfold zero toRealOrZero finiteValue; simp
theorem negZero_toReal : negZero.toRealOrZero =  0 := by
  unfold negZero toRealOrZero finiteValue; simp
theorem one_toReal     : one.toRealOrZero     =  1 := by
  unfold one toRealOrZero finiteValue; simp [bias]
theorem negOne_toReal  : negOne.toRealOrZero  = -1 := by
  unfold negOne toRealOrZero finiteValue; simp [bias]

theorem maxFinite_eq :
    maxFinite 8 23 = (2 - (2:ℝ) ^ (-(23:Int))) * (2:ℝ) ^ (127:Int) := by
  unfold maxFinite; norm_num [maxExp, bias]
theorem minPosSubnormal_eq :
    minPosSubnormal 8 23 = (2:ℝ) ^ (-(149:Int)) := by
  unfold minPosSubnormal; norm_num [minSubnormalExp, minNormalExp, bias]
theorem topUlp_eq :
    topUlp 8 23 = (2:ℝ) ^ ((127:Int) - 23) := by
  unfold topUlp; norm_num [maxExp, bias]

theorem toBits_zero    : toBits zero    = 0x00000000#32 := by decide
theorem toBits_negZero : toBits negZero = 0x80000000#32 := by decide
theorem toBits_one     : toBits one     = 0x3F800000#32 := by decide
theorem toBits_negOne  : toBits negOne  = 0xBF800000#32 := by decide
theorem toBits_smallestPosSubnormal :
    toBits smallestPosSubnormal = 0x00000001#32 := by decide
theorem toBits_maxFiniteEnc : toBits maxFiniteEnc = 0x7F7FFFFF#32 := by decide
theorem toBits_posInf  : toBits ((.inf false) : Binary32) = 0x7F800000#32 := by decide
theorem toBits_negInf  : toBits ((.inf true)  : Binary32) = 0xFF800000#32 := by decide
theorem toBits_nan     : toBits ((.nan)       : Binary32) = 0x7FC00000#32 := by decide

end Binary32

/-! ## Binary64 (IEEE 754 double precision)

  *  64 total bits — 1 sign, 11 exp, 52 mantissa
  *  bias = 1023, range ≈ 5×10⁻³²⁴ to 1.8×10³⁰⁸
  *  the standard for scientific computing -/

namespace Binary64

theorem bias_eq            : (bias 11 : Int)             =   1023 := by decide
theorem maxExp_eq          : (maxExp 11 : Int)           =   1023 := by decide
theorem minNormalExp_eq    : (minNormalExp 11 : Int)     =  -1022 := by decide
theorem minSubnormalExp_eq : (minSubnormalExp 11 52 : Int) = -1074 := by decide

/-- +0. -/
def zero : Binary64 := .finite false ⟨0, by decide⟩ ⟨0, by decide⟩
/-- −0. -/
def negZero : Binary64 := .finite true ⟨0, by decide⟩ ⟨0, by decide⟩
/-- +1.0. -/
def one : Binary64 := .finite false ⟨1023, by decide⟩ ⟨0, by decide⟩
/-- −1.0. -/
def negOne : Binary64 := .finite true ⟨1023, by decide⟩ ⟨0, by decide⟩
/-- The smallest positive subnormal: `2⁻¹⁰⁷⁴`. -/
def smallestPosSubnormal : Binary64 :=
  .finite false ⟨0, by decide⟩ ⟨1, by decide⟩
/-- The largest finite value: `(2 − 2⁻⁵²) · 2¹⁰²³`. -/
def maxFiniteEnc : Binary64 :=
  .finite false ⟨2 ^ 11 - 1 - 1, by decide⟩ ⟨2 ^ 52 - 1, by decide⟩

theorem zero_toReal    : zero.toRealOrZero    =  0 := by
  unfold zero toRealOrZero finiteValue; simp
theorem negZero_toReal : negZero.toRealOrZero =  0 := by
  unfold negZero toRealOrZero finiteValue; simp
theorem one_toReal     : one.toRealOrZero     =  1 := by
  unfold one toRealOrZero finiteValue; simp [bias]
theorem negOne_toReal  : negOne.toRealOrZero  = -1 := by
  unfold negOne toRealOrZero finiteValue; simp [bias]

theorem maxFinite_eq :
    maxFinite 11 52 = (2 - (2:ℝ) ^ (-(52:Int))) * (2:ℝ) ^ (1023:Int) := by
  unfold maxFinite; norm_num [maxExp, bias]
theorem minPosSubnormal_eq :
    minPosSubnormal 11 52 = (2:ℝ) ^ (-(1074:Int)) := by
  unfold minPosSubnormal; norm_num [minSubnormalExp, minNormalExp, bias]
theorem topUlp_eq :
    topUlp 11 52 = (2:ℝ) ^ ((1023:Int) - 52) := by
  unfold topUlp; norm_num [maxExp, bias]

theorem toBits_zero    : toBits zero    = 0x0000000000000000#64 := by decide
theorem toBits_negZero : toBits negZero = 0x8000000000000000#64 := by decide
theorem toBits_one     : toBits one     = 0x3FF0000000000000#64 := by decide
theorem toBits_negOne  : toBits negOne  = 0xBFF0000000000000#64 := by decide
theorem toBits_smallestPosSubnormal :
    toBits smallestPosSubnormal = 0x0000000000000001#64 := by decide
theorem toBits_maxFiniteEnc :
    toBits maxFiniteEnc = 0x7FEFFFFFFFFFFFFF#64 := by decide
theorem toBits_posInf  :
    toBits ((.inf false) : Binary64) = 0x7FF0000000000000#64 := by decide
theorem toBits_negInf  :
    toBits ((.inf true)  : Binary64) = 0xFFF0000000000000#64 := by decide
theorem toBits_nan     :
    toBits ((.nan)       : Binary64) = 0x7FF8000000000000#64 := by decide

end Binary64

/-! ## BFloat16 (Google brain-float)

  *  16 total bits — 1 sign, 8 exp, 7 mantissa
  *  bias = 127 (same as f32), but only 7-bit mantissa
  *  designed so the high half of an f32 bit pattern *is* a bf16 —
     truncate-to-cast, no separate rounding step needed
  *  used in TensorFlow / TPU / modern accelerators

`BFloat16` is *not* an IEEE 754 interchange format — the standard
doesn't define this width-eb-mb combination — but it follows IEEE
754's structural rules for sign / biased exponent / trailing
mantissa, so this library handles it uniformly. -/

namespace BFloat16

theorem bias_eq            : (bias 8 : Int)            =  127 := by decide
theorem maxExp_eq          : (maxExp 8 : Int)          =  127 := by decide
theorem minNormalExp_eq    : (minNormalExp 8 : Int)    = -126 := by decide
theorem minSubnormalExp_eq : (minSubnormalExp 8 7 : Int) = -133 := by decide

/-- +0. -/
def zero : BFloat16 := .finite false ⟨0, by decide⟩ ⟨0, by decide⟩
/-- −0. -/
def negZero : BFloat16 := .finite true ⟨0, by decide⟩ ⟨0, by decide⟩
/-- +1.0. -/
def one : BFloat16 := .finite false ⟨127, by decide⟩ ⟨0, by decide⟩
/-- −1.0. -/
def negOne : BFloat16 := .finite true ⟨127, by decide⟩ ⟨0, by decide⟩
/-- The smallest positive subnormal: `2⁻¹³³`. -/
def smallestPosSubnormal : BFloat16 :=
  .finite false ⟨0, by decide⟩ ⟨1, by decide⟩
/-- The largest finite value: `(2 − 2⁻⁷) · 2¹²⁷`. -/
def maxFiniteEnc : BFloat16 :=
  .finite false ⟨2 ^ 8 - 1 - 1, by decide⟩ ⟨2 ^ 7 - 1, by decide⟩

theorem zero_toReal    : zero.toRealOrZero    =  0 := by
  unfold zero toRealOrZero finiteValue; simp
theorem negZero_toReal : negZero.toRealOrZero =  0 := by
  unfold negZero toRealOrZero finiteValue; simp
theorem one_toReal     : one.toRealOrZero     =  1 := by
  unfold one toRealOrZero finiteValue; simp [bias]
theorem negOne_toReal  : negOne.toRealOrZero  = -1 := by
  unfold negOne toRealOrZero finiteValue; simp [bias]

theorem maxFinite_eq :
    maxFinite 8 7 = (2 - (2:ℝ) ^ (-(7:Int))) * (2:ℝ) ^ (127:Int) := by
  unfold maxFinite; norm_num [maxExp, bias]
theorem minPosSubnormal_eq :
    minPosSubnormal 8 7 = (2:ℝ) ^ (-(133:Int)) := by
  unfold minPosSubnormal; norm_num [minSubnormalExp, minNormalExp, bias]
theorem topUlp_eq :
    topUlp 8 7 = (2:ℝ) ^ ((127:Int) - 7) := by
  unfold topUlp; norm_num [maxExp, bias]

theorem toBits_zero    : toBits zero    = 0x0000#16 := by decide
theorem toBits_negZero : toBits negZero = 0x8000#16 := by decide
theorem toBits_one     : toBits one     = 0x3F80#16 := by decide
theorem toBits_negOne  : toBits negOne  = 0xBF80#16 := by decide
theorem toBits_smallestPosSubnormal :
    toBits smallestPosSubnormal = 0x0001#16 := by decide
theorem toBits_maxFiniteEnc : toBits maxFiniteEnc = 0x7F7F#16 := by decide
theorem toBits_posInf  : toBits ((.inf false) : BFloat16) = 0x7F80#16 := by decide
theorem toBits_negInf  : toBits ((.inf true)  : BFloat16) = 0xFF80#16 := by decide
theorem toBits_nan     : toBits ((.nan)       : BFloat16) = 0x7FC0#16 := by decide

end BFloat16

end IEEEFloat
