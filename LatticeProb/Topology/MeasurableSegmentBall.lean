import LatticeProb.LQG.MatingOfTreesCouplingSegments

/-! # Measurability of balls contained in variable curve segments -/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace LatticeProb

/-- The event that a continuous curve segment contains a closed ball is measurable
when the curve, endpoints and radius are measurable. -/
theorem measurableSet_exists_closedBall_subset_segment
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {f : Ω → C(ℝ, E)} {a b δ : Ω → ℝ}
    (hf : Measurable f) (ha : Measurable a) (hb : Measurable b) (hδ : Measurable δ) :
    MeasurableSet {ω | a ω ≤ b ω ∧ 0 ≤ δ ω ∧
      ∃ z, closedBall z (δ ω) ⊆ f ω '' Icc (a ω) (b ω)} := by
  let g : Ω → C(ℝ, E) := fun ω => ContinuousMap.segmentReparam (f ω, a ω, b ω)
  have hg : Measurable g :=
    ContinuousMap.segmentReparam.continuous.measurable.comp (hf.prodMk (ha.prodMk hb))
  have hball := (ContinuousMap.measurableSet_setOf_exists_closedBall_subset_image
    (E := E) (K := Icc (0 : ℝ) 1) isCompact_Icc).preimage (hg.prodMk hδ)
  have hab : MeasurableSet {ω | a ω ≤ b ω} := measurableSet_le ha hb
  convert hab.inter hball using 1
  ext ω
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨hab, hr, z, hz⟩
    exact ⟨hab, hr, z, by simpa only [g, ContinuousMap.segmentReparam_image_Icc _ hab] using hz⟩
  · rintro ⟨hab, hr, z, hz⟩
    exact ⟨hab, hr, z, by simpa only [g, ContinuousMap.segmentReparam_image_Icc _ hab] using hz⟩

end LatticeProb
