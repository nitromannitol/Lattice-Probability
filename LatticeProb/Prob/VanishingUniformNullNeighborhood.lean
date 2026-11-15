import LatticeProb.Prob.FiniteCompactNullNeighborhood

/-! # Vanishing neighborhoods for finite compact families of measures -/

set_option autoImplicit false

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace LatticeProb

/-- Neighborhood masses converge to zero uniformly over finitely many continuous
compact families of probability measures with a common closed null set. -/
theorem eventually_uniform_thickening_lt_of_finite_compact_null
    {X J A : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Fintype J]
    (P : J → Type*) [∀ j, TopologicalSpace (P j)] [∀ j, CompactSpace (P j)]
    (ν : ∀ j, P j → ProbabilityMeasure X) (hν : ∀ j, Continuous (ν j))
    (F : Set X) (hF : IsClosed F) (hnull : ∀ j p, (ν j p : Measure X) F = 0)
    (l : Filter A) (r : A → ℝ) (hr : Tendsto r l (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ a in l, ∀ j p, (ν j p : Measure X) (thickening (r a) F) < ε := by
  obtain ⟨t, ht, hbound⟩ :=
    exists_uniform_thickening_lt_of_finite_compact_null P ν hν F hF hnull hε
  have hsmall : ∀ᶠ a in l, r a < t := hr.eventually (Iio_mem_nhds ht)
  filter_upwards [hsmall] with a ha
  intro j p
  exact lt_of_le_of_lt (measure_mono (thickening_mono (le_of_lt ha) F)) (hbound j p)

end LatticeProb
