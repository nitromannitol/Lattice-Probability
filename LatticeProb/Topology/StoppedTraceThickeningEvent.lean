import LatticeProb.Topology.CompactPrefixInterval
import LatticeProb.Topology.CompactThickeningEvent

/-! # Compact containment in thickenings of stopped path traces -/

set_option autoImplicit false

open Set Metric MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace LatticeProb

/-- Compact containment in a thickening of a finite prefix is measurable from
an observed path and an extended clock, totalized to zero at infinity. -/
theorem measurableSet_compact_subset_thickening_compactPathPrefix
    {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]
    [MeasurableSpace (NonemptyCompacts E)] [BorelSpace (NonemptyCompacts E)]
    {v : Ω → C(ℝ≥0, E)} {T : Ω → ℝ≥0∞}
    (hv : Measurable v) (hT : Measurable T) {S : Set E} (hS : IsCompact S) (r : ℝ) :
    MeasurableSet {ω | S ⊆ thickening r (compactPathPrefix (v ω) (T ω).toNNReal : Set E)} :=
  measurableSet_compact_subset_thickening (measurable_compactPathPrefix_toNNReal hv hT) hS r

/-- For a pointwise finite clock, compact containment in a thickening of the
original trace is measurable from the stopped path and the clock. -/
theorem measurableSet_compact_subset_thickening_stoppedTrace
    {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]
    [MeasurableSpace (NonemptyCompacts E)] [BorelSpace (NonemptyCompacts E)]
    {w : Ω → C(ℝ≥0, E)} {T : Ω → ℝ≥0∞}
    (hw : Measurable (fun ω => stoppedPath (T ω) (w ω))) (hT : Measurable T)
    (hfinite : ∀ ω, T ω ≠ ∞) {S : Set E} (hS : IsCompact S) (r : ℝ) :
    MeasurableSet {ω | S ⊆ thickening r (w ω '' Icc 0 (T ω).toNNReal)} := by
  have h := measurableSet_compact_subset_thickening_compactPathPrefix hw hT hS r
  simpa only [coe_compactPathPrefix_stoppedPath _ _ (hfinite _)] using h

end LatticeProb
