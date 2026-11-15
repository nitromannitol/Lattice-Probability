import LatticeProb.Topology.CompactCurveRange

/-! # Compact ranges of finite path prefixes -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal unitInterval

namespace LatticeProb

/-- The nonempty compact range of a finite prefix of a continuous path. -/
def compactPathPrefix {E : Type*} [TopologicalSpace E]
    (w : C(ℝ≥0, E)) (T : ℝ≥0) : NonemptyCompacts E :=
  compactCurveRange (normalizedPathPrefix w T)

/-- The compact prefix varies continuously with the path and its finite duration. -/
theorem continuous_compactPathPrefix {E : Type*} [TopologicalSpace E] :
    Continuous (fun p : C(ℝ≥0, E) × ℝ≥0 => compactPathPrefix p.1 p.2) :=
  continuous_compactCurveRange.comp continuous_normalizedPathPrefix

/-- A compact prefix is measurable from a measurable path and finite clock. -/
theorem measurable_compactPathPrefix {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E]
    [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]
    [MeasurableSpace (NonemptyCompacts E)] [BorelSpace (NonemptyCompacts E)]
    {w : Ω → C(ℝ≥0, E)} {T : Ω → ℝ≥0} (hw : Measurable w) (hT : Measurable T) :
    Measurable (fun ω => compactPathPrefix (w ω) (T ω)) :=
  continuous_compactPathPrefix.measurable.comp (hw.prodMk hT)

/-- A compact prefix formed using an extended clock is measurable from the
clock and path. The clock is totalized to zero at infinity. -/
theorem measurable_compactPathPrefix_toNNReal {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]
    [MeasurableSpace (NonemptyCompacts E)] [BorelSpace (NonemptyCompacts E)]
    {w : Ω → C(ℝ≥0, E)} {T : Ω → ℝ≥0∞} (hw : Measurable w) (hT : Measurable T) :
    Measurable (fun ω => compactPathPrefix (w ω) (T ω).toNNReal) :=
  measurable_compactPathPrefix hw (ENNReal.measurable_toNNReal.comp hT)

/-- The code represents exactly the range of the normalized prefix. -/
@[simp] theorem coe_compactPathPrefix {E : Type*} [TopologicalSpace E]
    (w : C(ℝ≥0, E)) (T : ℝ≥0) :
    (compactPathPrefix w T : Set E) = range (normalizedPathPrefix w T) := rfl

end LatticeProb
