import LatticeProb.Prob.MarkedRectangleGeneration
import LatticeProb.Prob.MarkedBoxSemiringFinite
import LatticeProb.Prob.MarkedBoxCover

/-! Approximation in finite measure by finite unions of marked half-open boxes. -/

open Set MeasurableSpace MeasureTheory
open scoped ENNReal symmDiff

namespace LatticeProb

private theorem ico_countably_spanning :
    IsCountablySpanning {s : Set ℝ | ∃ u v : ℝ, s = Ico u v} := by
  refine ⟨fun n : ℕ => Ico (-(n : ℝ)) (n : ℝ), ?_, ?_⟩
  · intro n
    exact ⟨_, _, rfl⟩
  · ext x
    simp only [mem_iUnion, mem_Ico, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    refine ⟨n, ?_, ?_⟩
    · have := neg_abs_le x
      linarith
    · exact lt_of_le_of_lt (le_abs_self x) hn

/-- A measurable set can be approximated in finite measure by a finite union of
measurable marks times half-open boxes. -/
theorem exists_marked_Ico_boxes_measure_symmDiff_lt
    {E ι : Type*} [MeasurableSpace E] [Finite ι]
    (μ : Measure (E × (ι → ℝ))) [IsFiniteMeasure μ]
    {s : Set (E × (ι → ℝ))} (hs : MeasurableSet s)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ t ∈ supClosure (Set.image2 (· ×ˢ ·) {s : Set E | MeasurableSet s}
      (Set.univ.pi '' Set.univ.pi (fun _ : ι =>
        {s : Set ℝ | ∃ u v : ℝ, s = Ico u v}))), μ (t ∆ s) < ε := by
  apply exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring
    isSetSemiring_marked_Ico_boxes_finite
    (exists_countable_cover_marked_boxes_ae (fun _ => ico_countably_spanning) μ)
    generateFrom_marked_Ico_boxes.symm hs hε

/-- A finite family of marked half-open boxes approximates a measurable set
in any finite measure. -/
theorem exists_finset_marked_Ico_boxes_measure_symmDiff_lt
    {E ι : Type*} [MeasurableSpace E] [Finite ι]
    (μ : Measure (E × (ι → ℝ))) [IsFiniteMeasure μ]
    {s : Set (E × (ι → ℝ))} (hs : MeasurableSet s)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ F : Finset (Set (E × (ι → ℝ))),
      (↑F : Set (Set (E × (ι → ℝ)))) ⊆
        Set.image2 (· ×ˢ ·) {s : Set E | MeasurableSet s}
          (Set.univ.pi '' Set.univ.pi (fun _ : ι =>
            {s : Set ℝ | ∃ u v : ℝ, s = Ico u v})) ∧
      μ ((⋃ t ∈ F, t) ∆ s) < ε := by
  obtain ⟨t, ⟨F, hF, hsub, rfl⟩, ht⟩ :=
    exists_marked_Ico_boxes_measure_symmDiff_lt μ hs hε
  refine ⟨F, hsub, ?_⟩
  simpa only [Finset.sup'_eq_sup, Finset.sup_set_eq_biUnion, id_eq] using ht

end LatticeProb
