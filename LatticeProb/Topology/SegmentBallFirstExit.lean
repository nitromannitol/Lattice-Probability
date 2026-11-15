import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTSegmentsContainBalls

/-! # Ball witnesses in first-exit traces -/

set_option autoImplicit false

open Set Metric

namespace LatticeProb

/-- A segment-ball estimate supplies a centered ball in a forward exit trace,
using the first exit from a strictly smaller ball. -/
theorem centered_ball_subset_forward_exit_of_segments
    (c : C(ℝ, ℂ)) {q ρ r ε δ : ℝ}
    (hc0 : c 0 = 0) (hq : 0 < q) (hqρ : q < ρ) (hρ : ρ ≤ 1)
    (hδ : δ ∈ Ioc (0 : ℝ) ε) (hδq : δ ^ (1 - r) ≤ q)
    (hsegments : MatedCRTHarmonic.MatedCRT.SegmentsContainBalls c ρ r ε)
    (hexit : {t : ℝ | 0 ≤ t ∧ c t ∉ ball 0 (1 : ℝ)}.Nonempty) :
    ∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
      c '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ c t ∉ ball 0 (1 : ℝ)}) := by
  let S : Set ℝ := {t | 0 ≤ t ∧ c t ∉ ball 0 q}
  have hclosed : IsClosed S := isClosed_Ici.inter (isOpen_ball.isClosed_compl.preimage c.continuous)
  have hbounded : BddBelow S := ⟨0, fun _ ht => ht.1⟩
  have hne : S.Nonempty := by
    obtain ⟨t, ht, hout⟩ := hexit
    refine ⟨t, ht, fun hin => hout ?_⟩
    exact ball_subset_ball (le_trans (le_of_lt hqρ) hρ) hin
  let τ := sInf S
  have hτ : τ ∈ S := hclosed.csInf_mem hne hbounded
  have hτpos : 0 < τ := by
    have hzero : (0 : ℝ) ∉ S := by simp [S, hc0, hq]
    exact lt_of_le_of_ne hτ.1 (fun h => hzero (h ▸ hτ))
  have hbefore : ∀ t ∈ Ico (0 : ℝ) τ, c t ∈ ball 0 q := by
    intro t ht
    by_contra hout
    exact (not_le_of_gt ht.2) (csInf_le hbounded ⟨ht.1, hout⟩)
  have hτclosed : c τ ∈ closedBall (0 : ℂ) q := by
    have hset : IsClosed (c ⁻¹' closedBall (0 : ℂ) q) := isClosed_closedBall.preimage c.continuous
    have hsub : Ico (0 : ℝ) τ ⊆ c ⁻¹' closedBall (0 : ℂ) q :=
      fun t ht => ball_subset_closedBall (hbefore t ht)
    have hmem : τ ∈ closure (Ico (0 : ℝ) τ) := by
      rw [closure_Ico (ne_of_lt hτpos)]
      exact ⟨hτpos.le, le_rfl⟩
    exact hset.closure_subset_iff.mpr hsub hmem
  have hinside : c '' Icc 0 τ ⊆ ball (0 : ℂ) ρ := by
    rintro x ⟨t, ht, rfl⟩
    by_cases htτ : t = τ
    · rw [htτ]
      exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hτclosed) hqρ)
    · exact ball_subset_ball (le_of_lt hqρ) (hbefore t ⟨ht.1, lt_of_le_of_ne ht.2 htτ⟩)
  have hdiam : q ≤ diam (c '' Icc 0 τ) := by
    have hbdd : Bornology.IsBounded (c '' Icc 0 τ) := (isCompact_Icc.image c.continuous).isBounded
    have hd := dist_le_diam_of_mem hbdd (mem_image_of_mem c ⟨le_rfl, hτpos.le⟩)
      (mem_image_of_mem c ⟨hτpos.le, le_rfl⟩)
    have hout : q ≤ dist (c 0) (c τ) := by
      have := not_lt.mp (show ¬ dist (c τ) 0 < q from hτ.2)
      simpa [hc0, dist_comm] using this
    exact hout.trans hd
  obtain ⟨z, hz⟩ := hsegments δ hδ 0 τ hτpos hinside (hδq.trans hdiam)
  have hzρ : z ∈ ball (0 : ℂ) ρ := hinside (hz (mem_ball_self hδ.1))
  have hτle : τ ≤ sInf {t : ℝ | 0 ≤ t ∧ c t ∉ ball 0 (1 : ℝ)} := by
    apply le_csInf hexit
    intro t ht
    exact csInf_le hbounded ⟨ht.1, fun hin => ht.2 (ball_subset_ball (le_trans (le_of_lt hqρ) hρ) hin)⟩
  exact ⟨z, hzρ, hz.trans (image_mono (Icc_subset_Icc le_rfl hτle))⟩

end LatticeProb
