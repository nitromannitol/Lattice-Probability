import LatticeProb.Topology.SegmentBallFirstExit

/-! # Time reversal and centered first-exit ball witnesses -/

set_option autoImplicit false

open Set Metric

namespace LatticeProb

/-- Time reversal preserves the segment-ball event. -/
theorem segmentsContainBalls_reverse (c : C(ℝ, ℂ)) {ρ r ε : ℝ}
    (hsegments : MatedCRTHarmonic.MatedCRT.SegmentsContainBalls c ρ r ε) :
    MatedCRTHarmonic.MatedCRT.SegmentsContainBalls
      (c.comp ⟨fun t : ℝ => -t, continuous_neg⟩) ρ r ε := by
  intro δ hδ a b hab hinside hdiam
  let d : C(ℝ, ℂ) := c.comp ⟨fun t : ℝ => -t, continuous_neg⟩
  have himage : d '' Icc a b = c '' Icc (-b) (-a) := by
    ext x
    constructor
    · rintro ⟨t, ⟨hta, htb⟩, rfl⟩
      exact ⟨-t, ⟨by linarith, by linarith⟩, rfl⟩
    · rintro ⟨t, ⟨htb, hta⟩, rfl⟩
      refine ⟨-t, ⟨by linarith, by linarith⟩, ?_⟩
      simp only [d, ContinuousMap.comp_apply, ContinuousMap.coe_mk, neg_neg]
  change d '' Icc a b ⊆ ball 0 ρ at hinside
  change δ ^ (1 - r) ≤ diam (d '' Icc a b) at hdiam
  change ∃ w, ball w δ ⊆ d '' Icc a b
  rw [himage] at hinside hdiam ⊢
  exact hsegments δ hδ (-b) (-a) (by linarith) hinside hdiam

/-- A segment-ball event and a backward exit give a centered ball in the
backward first-exit trace. -/
theorem centered_ball_subset_backward_exit_of_segments
    (c : C(ℝ, ℂ)) {q ρ r ε δ : ℝ}
    (hc0 : c 0 = 0) (hq : 0 < q) (hqρ : q < ρ) (hρ : ρ ≤ 1)
    (hδ : δ ∈ Ioc (0 : ℝ) ε) (hδq : δ ^ (1 - r) ≤ q)
    (hsegments : MatedCRTHarmonic.MatedCRT.SegmentsContainBalls c ρ r ε)
    (hexit : {t : ℝ | t ≤ 0 ∧ c t ∉ ball 0 (1 : ℝ)}.Nonempty) :
    ∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
      c '' Icc (sSup {t : ℝ | t ≤ 0 ∧ c t ∉ ball 0 (1 : ℝ)}) 0 := by
  let d : C(ℝ, ℂ) := c.comp ⟨fun t : ℝ => -t, continuous_neg⟩
  let A : Set ℝ := {t | t ≤ 0 ∧ c t ∉ ball 0 (1 : ℝ)}
  have htimes : {t : ℝ | 0 ≤ t ∧ d t ∉ ball 0 (1 : ℝ)} = -A := by
    ext t
    simp only [mem_ofPred_eq, mem_neg, A, d, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, neg_nonpos]
  have hforward : {t : ℝ | 0 ≤ t ∧ d t ∉ ball 0 (1 : ℝ)}.Nonempty := by
    obtain ⟨t, ht, hout⟩ := hexit
    exact ⟨-t, by linarith, by simpa [d] using hout⟩
  have hendpoint : sInf {t : ℝ | 0 ≤ t ∧ d t ∉ ball 0 (1 : ℝ)} = -sSup A := by
    rw [htimes, Real.sInf_neg]
  have htrace : d '' Icc 0 (-sSup A) = c '' Icc (sSup A) 0 := by
    ext x
    constructor
    · rintro ⟨t, ⟨ht₀, ht⟩, rfl⟩
      exact ⟨-t, ⟨by linarith, by linarith⟩, rfl⟩
    · rintro ⟨t, ⟨ht, ht₀⟩, rfl⟩
      refine ⟨-t, ⟨by linarith, by linarith⟩, ?_⟩
      simp only [d, ContinuousMap.comp_apply, ContinuousMap.coe_mk, neg_neg]
  have hroot : d 0 = 0 := by simpa [d] using hc0
  obtain ⟨z, hz, hball⟩ := centered_ball_subset_forward_exit_of_segments d hroot hq hqρ hρ
    hδ hδq (segmentsContainBalls_reverse c hsegments) hforward
  rw [hendpoint, htrace] at hball
  exact ⟨z, hz, hball⟩

/-- The same segment-ball event supplies witnesses on both sides of the root. -/
theorem centered_ball_subset_both_exits_of_segments
    (c : C(ℝ, ℂ)) {q ρ r ε δ : ℝ}
    (hc0 : c 0 = 0) (hq : 0 < q) (hqρ : q < ρ) (hρ : ρ ≤ 1)
    (hδ : δ ∈ Ioc (0 : ℝ) ε) (hδq : δ ^ (1 - r) ≤ q)
    (hsegments : MatedCRTHarmonic.MatedCRT.SegmentsContainBalls c ρ r ε)
    (hleft : {t : ℝ | t ≤ 0 ∧ c t ∉ ball 0 (1 : ℝ)}.Nonempty)
    (hright : {t : ℝ | 0 ≤ t ∧ c t ∉ ball 0 (1 : ℝ)}.Nonempty) :
    (∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
      c '' Icc (sSup {t : ℝ | t ≤ 0 ∧ c t ∉ ball 0 (1 : ℝ)}) 0) ∧
    (∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
      c '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ c t ∉ ball 0 (1 : ℝ)})) := by
  exact ⟨centered_ball_subset_backward_exit_of_segments c hc0 hq hqρ hρ hδ hδq hsegments hleft,
    centered_ball_subset_forward_exit_of_segments c hc0 hq hqρ hρ hδ hδq hsegments hright⟩

end LatticeProb
