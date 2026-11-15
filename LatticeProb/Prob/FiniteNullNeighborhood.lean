import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-! # Neighborhoods of a common null closed set -/

set_option autoImplicit false

open MeasureTheory Set Metric Filter
open scoped Topology ENNReal

namespace LatticeProb

/-- A finite family of finite measures gives uniformly small mass to a sufficiently
small neighborhood of a closed set that is null for every measure in the family. -/
theorem exists_uniform_thickening_lt_of_finite_null
    {X ι : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [Fintype ι] (μ : ι → Measure X) [∀ i, IsFiniteMeasure (μ i)]
    (F : Set X) (hF : IsClosed F) (hnull : ∀ i, μ i F = 0)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ i, μ i (thickening r F) < ε := by
  classical
  have hone : ∀ i, ∃ r : ℝ, 0 < r ∧ μ i (cthickening r F) < ε := by
    intro i
    have ht : Tendsto (fun r : ℝ => μ i (cthickening r F)) (𝓝 0) (𝓝 0) := by
      simpa only [hnull i] using
        (tendsto_measure_cthickening_of_isClosed (μ := μ i)
          ⟨1, zero_lt_one, measure_ne_top (μ i) _⟩ hF)
    have he : ∀ᶠ r in 𝓝 (0 : ℝ), μ i (cthickening r F) < ε :=
      ht.eventually (eventually_lt_nhds hε)
    obtain ⟨δ, hδ, hδprop⟩ := Metric.eventually_nhds_iff.mp he
    refine ⟨δ / 2, half_pos hδ, hδprop ?_⟩
    simpa [Real.dist_eq, abs_of_pos (half_pos hδ)] using half_lt_self hδ
  have hfin : ∀ s : Finset ι, ∃ r : ℝ, 0 < r ∧
      ∀ i ∈ s, μ i (cthickening r F) < ε := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨r, hr, hri⟩ := ih
      obtain ⟨t, ht, hta⟩ := hone a
      refine ⟨min r t, lt_min hr ht, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact lt_of_le_of_lt (measure_mono (cthickening_mono (min_le_right r t) F)) hta
      · exact lt_of_le_of_lt (measure_mono (cthickening_mono (min_le_left r t) F)) (hri i hi)
  obtain ⟨r, hr, hri⟩ := hfin Finset.univ
  exact ⟨r, hr, fun i => lt_of_le_of_lt
    (measure_mono (thickening_subset_cthickening r F)) (hri i (Finset.mem_univ i))⟩

end LatticeProb
