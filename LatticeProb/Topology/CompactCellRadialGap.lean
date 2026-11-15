import LatticeProb.Topology.CompactCurveRange
import Mathlib.Topology.MetricSpace.Closeds

/-! # Measurable radial gaps for compact cells -/

set_option autoImplicit false

namespace LatticeProb

open MeasureTheory Set

/-- For a measurable countable family of nonempty compact sets, the event that
no set has its distance from a fixed point in a given open interval is Borel. -/
theorem measurableSet_compactCell_radial_gap
    {Ω ι E : Type*} [MeasurableSpace Ω] [Countable ι] [MetricSpace E]
    [MeasurableSpace (TopologicalSpace.NonemptyCompacts E)]
    [BorelSpace (TopologicalSpace.NonemptyCompacts E)]
    (C : ι → Ω → TopologicalSpace.NonemptyCompacts E)
    (hC : ∀ i, Measurable (C i)) (z : E) (a b : ℝ) :
    MeasurableSet {ω | ∀ i, Metric.infDist z (C i ω : Set E) ≤ a ∨
      b ≤ Metric.infDist z (C i ω : Set E)} := by
  have hdist (i : ι) : Measurable (fun ω => Metric.infDist z (C i ω : Set E)) :=
    (TopologicalSpace.NonemptyCompacts.lipschitz_infDist_const z).continuous.measurable.comp (hC i)
  have h : MeasurableSet (⋂ i : ι, {ω | Metric.infDist z (C i ω : Set E) ≤ a} ∪
      {ω | b ≤ Metric.infDist z (C i ω : Set E)}) :=
    MeasurableSet.iInter fun i =>
      (measurableSet_le (hdist i) measurable_const).union
        (measurableSet_le measurable_const (hdist i))
  convert h using 1
  ext ω
  simp only [mem_ofPred_eq, mem_iInter, mem_union]

/-- A radial gap for the shifted cells of a measurable continuous curve is a
measurable event jointly in the curve, mesh and phase. -/
theorem measurableSet_shiftedCompactCell_radial_gap
    {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    [MeasurableSpace C(ℝ, E)] [BorelSpace C(ℝ, E)]
    [MeasurableSpace (TopologicalSpace.NonemptyCompacts E)]
    [BorelSpace (TopologicalSpace.NonemptyCompacts E)]
    (η : Ω → C(ℝ, E)) (ε θ : Ω → ℝ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (z : E) (a b : ℝ) :
    MeasurableSet {ω | ∀ k : ℤ,
      Metric.infDist z (shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set E) ≤ a ∨
        b ≤ Metric.infDist z (shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set E)} := by
  apply measurableSet_compactCell_radial_gap
  intro k
  exact (measurable_shiftedCompactCell k).comp (hη.prodMk (hε.prodMk hθ))

end LatticeProb
