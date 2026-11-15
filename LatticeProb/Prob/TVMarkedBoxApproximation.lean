import LatticeProb.Prob.DisjointMarkedBoxApproximation
import LatticeProb.Bonanno.QuantumZipper.Proofs.Section5.TVLocal

/-! Total variation approximation of restrictions by marked boxes. -/

open Set MeasureTheory
open scoped ENNReal symmDiff

namespace LatticeProb

/-- Restricting a measure to two sets changes it in total variation by at
most the measure of their symmetric difference. -/
theorem tvDist_restrict_le_measure_symmDiff {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s t : Set α) :
    QuantumZipper.TV.tvDist (μ.restrict s) (μ.restrict t) ≤ μ (s ∆ t) := by
  have bound (s t u : Set α) : μ (u ∩ s) ≤ μ (u ∩ t) + μ (s ∆ t) := by
    calc
      μ (u ∩ s) ≤ μ ((u ∩ t) ∪ (s ∆ t)) := by
        apply measure_mono
        intro x hx
        by_cases ht : x ∈ t
        · exact Or.inl ⟨hx.1, ht⟩
        · exact Or.inr (Set.mem_symmDiff.mpr (Or.inl ⟨hx.2, ht⟩))
      _ ≤ μ (u ∩ t) + μ (s ∆ t) := measure_union_le _ _
  refine iSup_le fun u => iSup_le fun hu => sup_le ?_ ?_
  · rw [Measure.restrict_apply hu, Measure.restrict_apply hu]
    exact tsub_le_iff_left.mpr (bound s t u)
  · rw [Measure.restrict_apply hu, Measure.restrict_apply hu]
    exact tsub_le_iff_left.mpr (by simpa only [symmDiff_comm] using bound t s u)

/-- In a finite measure, each measurable restriction is approximated in total
variation by restriction to a finite disjoint union of marked boxes. -/
theorem exists_disjoint_finset_marked_Ico_boxes_tv_restrict_lt
    {E ι : Type*} [MeasurableSpace E] [Finite ι]
    (μ : Measure (E × (ι → ℝ))) [IsFiniteMeasure μ]
    {s : Set (E × (ι → ℝ))} (hs : MeasurableSet s)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ F : Finset (Set (E × (ι → ℝ))),
      (↑F : Set (Set (E × (ι → ℝ)))) ⊆
        Set.image2 (· ×ˢ ·) {s : Set E | MeasurableSet s}
          (Set.univ.pi '' Set.univ.pi (fun _ : ι =>
            {s : Set ℝ | ∃ u v : ℝ, s = Ico u v})) ∧
      (↑F : Set (Set (E × (ι → ℝ)))).PairwiseDisjoint id ∧
      QuantumZipper.TV.tvDist (μ.restrict (⋃ t ∈ F, t)) (μ.restrict s) < ε := by
  obtain ⟨F, hF, hdisj, hμ⟩ :=
    exists_disjoint_finset_marked_Ico_boxes_measure_symmDiff_lt μ hs hε
  exact ⟨F, hF, hdisj, (tvDist_restrict_le_measure_symmDiff μ _ _).trans_lt hμ⟩

end LatticeProb
