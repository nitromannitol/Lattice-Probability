import LatticeProb.Prob.LocalizedSimpleDensityPhase
import LatticeProb.Prob.TVMarkedBoxApproximation
import Mathlib.MeasureTheory.Measure.Continuity

/-! Transfer of phase convergence through finite-measure exhaustions. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology symmDiff

namespace LatticeProb

/-- Restrictions to an increasing measurable cover approximate a finite measure
in total variation. -/
theorem exists_restrict_tvDist_lt_of_iUnion_eq_univ
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : ℕ → Set α) (hB : ∀ k, MeasurableSet (B k))
    (hmono : Monotone B) (hcover : (⋃ k, B k) = univ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ k, QuantumZipper.TV.tvDist μ (μ.restrict (B k)) < ε := by
  have hanti : Antitone (fun k => (B k)ᶜ) := fun i j hij =>
    compl_subset_compl.mpr (hmono hij)
  have hinter : (⋂ k, (B k)ᶜ) = ∅ := by
    rw [← compl_iUnion, hcover, compl_univ]
  have hlim : Tendsto (fun k => μ (B k)ᶜ) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ)
      (fun k => (hB k).compl.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    simpa only [hinter, measure_empty, Function.comp_def] using h
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  refine ⟨k, lt_of_le_of_lt ?_ hk⟩
  have hsym : univ ∆ B k = (B k)ᶜ := by
    ext x
    simp only [mem_symmDiff, mem_univ, true_and, not_true_eq_false, and_false, or_false, mem_compl_iff]
  simpa only [Measure.restrict_univ, hsym] using
    (tvDist_restrict_le_measure_symmDiff μ univ (B k))

/-- Phase convergence on an increasing measurable cover transfers to the full
finite measure. -/
theorem tendsto_tvDist_map_prod_unitCube_of_exhaustion
    {E X ι τ : Type*} [MeasurableSpace E] [MeasurableSpace X] [Fintype ι]
    {l : Filter τ} (μ : Measure (E × X)) [IsFiniteMeasure μ]
    (g : τ → E × X → E × (ι → ℝ)) (hg : ∀ t, Measurable (g t))
    (B : ℕ → Set (E × X)) (hB : ∀ k, MeasurableSet (B k))
    (hmono : Monotone B) (hcover : (⋃ k, B k) = univ)
    (hphase : ∀ k, Tendsto (fun t => QuantumZipper.TV.tvDist
      ((μ.restrict (B k)).map (g t))
      (((μ.restrict (B k)).map Prod.fst).prod (unitCubeMeasure ι))) l (𝓝 0)) :
    Tendsto (fun t => QuantumZipper.TV.tvDist (μ.map (g t))
      ((μ.map Prod.fst).prod (unitCubeMeasure ι))) l (𝓝 0) := by
  apply tendsto_tvDist_map_prod_unitCube_of_exists_approx μ g hg
  intro ε hε
  obtain ⟨k, hk⟩ := exists_restrict_tvDist_lt_of_iUnion_eq_univ μ B hB hmono hcover hε
  exact ⟨μ.restrict (B k), inferInstance, hk, hphase k⟩

end LatticeProb
