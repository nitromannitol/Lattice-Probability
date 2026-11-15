import LatticeProb.Topology.ObservedSegmentBall

/-! # Centered balls in measurable curve segments -/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace LatticeProb

/-- A positive-radius ball contained in a measurable curve segment can be
required to have its center in a prescribed open ball measurably. -/
theorem measurableSet_exists_centered_ball_subset_segment
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {f : Ω → C(ℝ, E)} {a b : Ω → ℝ}
    (hf : Measurable f) (ha : Measurable a) (hb : Measurable b)
    (ρ δ : ℝ) (hδ : 0 < δ) :
    MeasurableSet {ω | a ω ≤ b ω ∧ ∃ z ∈ ball (0 : E) ρ,
      ball z δ ⊆ f ω '' Icc (a ω) (b ω)} := by
  let g : Ω → C(ℝ, E) := fun ω => ContinuousMap.segmentReparam (f ω, a ω, b ω)
  have hg : Measurable g :=
    ContinuousMap.segmentReparam.continuous.measurable.comp (hf.prodMk (ha.prodMk hb))
  have hq (q : ℚ) : MeasurableSet {ω | ∃ z ∈ closedBall (0 : E) (q : ℝ),
      closedBall z δ ⊆ g ω '' Icc (0 : ℝ) 1} := by
    have h := (ContinuousMap.isClosed_setOf_closedBall_subset_image
      (E := E) (K := Icc (0 : ℝ) 1) isCompact_Icc (q : ℝ)).measurableSet.preimage
        (hg.prodMk (measurable_const : Measurable (fun _ : Ω => δ)))
    convert h using 1
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, hδ.le, true_and]
  have he : MeasurableSet (⋃ q : {q : ℚ // (q : ℝ) < ρ},
      {ω | ∃ z ∈ closedBall (0 : E) (q.1 : ℝ),
        closedBall z δ ⊆ g ω '' Icc (0 : ℝ) 1}) :=
    MeasurableSet.iUnion fun q => hq q.1
  convert (measurableSet_le ha hb).inter he using 1
  ext ω
  simp only [mem_ofPred_eq, mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨hab, z, hz, hzball⟩
    obtain ⟨q, hqz, hqρ⟩ := exists_rat_btwn (mem_ball_zero_iff.mp hz)
    refine ⟨hab, ⟨q, hqρ⟩, z, mem_closedBall_zero_iff.mpr hqz.le, ?_⟩
    rw [ContinuousMap.segmentReparam_image_Icc _ hab]
    exact (ball_subset_segment_iff_closedBall (f ω) (a ω) (b ω) δ hδ z).mp hzball
  · rintro ⟨hab, ⟨q, hqρ⟩, z, hz, hzball⟩
    refine ⟨hab, z, mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt hqρ), ?_⟩
    apply ball_subset_closedBall.trans
    rw [← ContinuousMap.segmentReparam_image_Icc _ hab]
    exact hzball

end LatticeProb
