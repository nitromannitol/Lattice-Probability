import LatticeProb.Prob.FiniteMeasureStandardBorel
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-! # Uniform neighborhoods of common null closed sets -/

set_option autoImplicit false

open MeasureTheory Set Metric Filter
open scoped Topology ENNReal

namespace LatticeProb

/-- A continuous family of probability measures on a compact parameter space
assigns uniformly small mass to a sufficiently small neighborhood of a common
closed null set. -/
theorem exists_uniform_thickening_lt_of_compact_null
    {X P : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace P] [CompactSpace P]
    (ν : P → ProbabilityMeasure X) (hν : Continuous ν)
    (F : Set X) (hF : IsClosed F) (hnull : ∀ p, (ν p : Measure X) F = 0)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ p, (ν p : Measure X) (thickening r F) < ε := by
  classical
  have hone : ∀ p, ∃ r : ℝ, 0 < r ∧ (ν p : Measure X) (cthickening r F) < ε := by
    intro p
    have ht : Tendsto (fun r : ℝ => (ν p : Measure X) (cthickening r F)) (𝓝 0) (𝓝 0) := by
      simpa only [hnull p] using
        (tendsto_measure_cthickening_of_isClosed (μ := (ν p : Measure X))
          ⟨1, zero_lt_one, measure_ne_top _ _⟩ hF)
    have he : ∀ᶠ r in 𝓝 (0 : ℝ), (ν p : Measure X) (cthickening r F) < ε :=
      ht.eventually (eventually_lt_nhds hε)
    obtain ⟨δ, hδ, hδprop⟩ := Metric.eventually_nhds_iff.mp he
    refine ⟨δ / 2, half_pos hδ, hδprop ?_⟩
    simpa [Real.dist_eq, abs_of_pos hδ] using half_lt_self hδ
  choose r hr hrbound using hone
  let U : P → Set P := fun p => {q | (ν q : Measure X) (cthickening (r p) F) < ε}
  have hU : ∀ p, IsOpen (U p) := by
    intro p
    exact hν.isOpen_preimage _ ((probabilityMeasure_usc_of_isClosed isClosed_cthickening).isOpen_preimage ε)
  have hcover : (univ : Set P) ⊆ ⋃ p, U p := by
    intro p hp
    exact mem_iUnion.mpr ⟨p, hrbound p⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  have hfin : ∀ s : Finset P, ∃ t : ℝ, 0 < t ∧
      ∀ p ∈ s, ∀ q ∈ U p, (ν q : Measure X) (cthickening t F) < ε := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert p s hp ih =>
      obtain ⟨t, ht, hts⟩ := ih
      refine ⟨min (r p) t, lt_min (hr p) ht, ?_⟩
      intro a ha q hq
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact lt_of_le_of_lt (measure_mono (cthickening_mono (min_le_left _ _) F)) hq
      · exact lt_of_le_of_lt (measure_mono (cthickening_mono (min_le_right _ _) F)) (hts a ha q hq)
  obtain ⟨t, ht, hts⟩ := hfin s
  refine ⟨t, ht, ?_⟩
  intro q
  obtain ⟨p, hp, hq⟩ := mem_iUnion₂.mp (hs (mem_univ q))
  exact lt_of_le_of_lt (measure_mono (thickening_subset_cthickening t F)) (hts p hp q hq)

end LatticeProb
