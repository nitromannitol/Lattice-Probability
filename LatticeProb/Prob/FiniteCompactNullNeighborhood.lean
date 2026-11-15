import LatticeProb.Prob.CompactNullNeighborhood

/-! # Uniform null neighborhoods for finitely many compact families -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb

/-- Finitely many continuous compact families of probability measures assign
uniformly small mass to a sufficiently small neighborhood of a common closed
null set. -/
theorem exists_uniform_thickening_lt_of_finite_compact_null
    {X J : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Fintype J]
    (P : J → Type*) [∀ j, TopologicalSpace (P j)] [∀ j, CompactSpace (P j)]
    (ν : ∀ j, P j → ProbabilityMeasure X) (hν : ∀ j, Continuous (ν j))
    (F : Set X) (hF : IsClosed F) (hnull : ∀ j p, (ν j p : Measure X) F = 0)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ j p, (ν j p : Measure X) (thickening r F) < ε := by
  classical
  have hone : ∀ j, ∃ r : ℝ, 0 < r ∧
      ∀ p, (ν j p : Measure X) (thickening r F) < ε := by
    intro j
    exact exists_uniform_thickening_lt_of_compact_null (ν j) (hν j) F hF (hnull j) hε
  choose r hr hbound using hone
  have hfin : ∀ s : Finset J, ∃ t : ℝ, 0 < t ∧
      ∀ j ∈ s, ∀ p, (ν j p : Measure X) (thickening t F) < ε := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert j s hj ih =>
      obtain ⟨t, ht, hts⟩ := ih
      refine ⟨min (r j) t, lt_min (hr j) ht, ?_⟩
      intro k hk p
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact lt_of_le_of_lt (measure_mono (thickening_mono (min_le_left _ _) F)) (hbound k p)
      · exact lt_of_le_of_lt (measure_mono (thickening_mono (min_le_right _ _) F)) (hts k hk p)
  obtain ⟨t, ht, hts⟩ := hfin Finset.univ
  exact ⟨t, ht, fun j p => hts j (Finset.mem_univ j) p⟩

end LatticeProb
