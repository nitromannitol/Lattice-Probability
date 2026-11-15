import LatticeProb.Prob.MarkedBoxApproximation

/-! Disjoint marked-box approximations in finite measure. -/

open Set MeasurableSpace MeasureTheory
open scoped ENNReal symmDiff

namespace LatticeProb

/-- Every measurable set can be approximated in finite measure by a finite
pairwise-disjoint family of marked half-open boxes. -/
theorem exists_disjoint_finset_marked_Ico_boxes_measure_symmDiff_lt
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
      μ ((⋃ t ∈ F, t) ∆ s) < ε := by
  obtain ⟨t, ht, hμ⟩ := exists_marked_Ico_boxes_measure_symmDiff_lt μ hs hε
  obtain ⟨P, hP⟩ := isSetSemiring_marked_Ico_boxes_finite.mem_supClosure_iff.mp ht
  refine ⟨P.parts, hP, P.disjoint, ?_⟩
  have h : (⋃ t ∈ P.parts, t) = t := by
    simpa only [Finset.sup_set_eq_biUnion, id_eq] using P.sup_parts
  simpa only [h] using hμ

end LatticeProb
