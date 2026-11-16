import LatticeProb.Prob.FiniteMeasureLevyProkhorov
import Mathlib.Topology.ContinuousMap.Compact

/-! # Comparison of decorated finite measures -/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace LatticeProb

/-- The sum of the Lévy–Prokhorov distance, the uniform distance of two full curves,
    and the distances of finitely many corresponding marks varies continuously. -/
theorem continuous_decoratedMeasureComparison
    {Z X T ι : Type*} [TopologicalSpace Z] [PseudoMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [TopologicalSpace T] [CompactSpace T]
    [Fintype ι]
    {μ ν : Z → FiniteMeasure X} {η ξ : Z → C(T, X)} {m n : Z → ι → X}
    (hμ : Continuous μ) (hν : Continuous ν) (hη : Continuous η) (hξ : Continuous ξ)
    (hm : Continuous m) (hn : Continuous n) :
    Continuous (fun z =>
      levyProkhorovDist ((μ z : FiniteMeasure X) : Measure X) ((ν z : FiniteMeasure X) : Measure X) +
      dist (η z) (ξ z) + ∑ i, dist (m z i) (n z i)) := by
  have hp : Continuous (fun z =>
      dist (LevyProkhorov.ofMeasure (μ z)) (LevyProkhorov.ofMeasure (ν z))) :=
    (continuous_levyProkhorov_ofMeasure_finiteMeasure.comp hμ).dist
      (continuous_levyProkhorov_ofMeasure_finiteMeasure.comp hν)
  have hc : Continuous (fun z => dist (η z) (ξ z)) := hη.dist hξ
  have hmarks : Continuous (fun z => ∑ i, dist (m z i) (n z i)) := by
    apply continuous_finsetSum
    intro i hi
    exact ((continuous_apply i).comp hm).dist ((continuous_apply i).comp hn)
  change Continuous (fun z =>
    dist (LevyProkhorov.ofMeasure (μ z)) (LevyProkhorov.ofMeasure (ν z)) +
      dist (η z) (ξ z) + ∑ i, dist (m z i) (n z i))
  exact (hp.add hc).add hmarks

end LatticeProb
