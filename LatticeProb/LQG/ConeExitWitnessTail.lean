import LatticeProb.Topology.SegmentBallExitReversal
import LatticeProb.Topology.FirstExitTraceTimeChange
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling

/-! # Joint first-exit witness bounds for the coupled cone curve -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Metric LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal Topology

namespace LatticeProb.LQG

/-- The segment-ball estimate bounds failure of both centered first-exit
witnesses for the area-parametrized curve. -/
theorem measure_joint_exit_witness_failure_le
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {q ρ r : ℝ} (hq : 0 < q) (hqρ : q < ρ) (hρ : ρ < 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) (N : ℕ) :
    ∃ C : ℝ, ∀ {δ : ℝ}, δ ∈ Ioo (0 : ℝ) 1 → δ ^ (1 - r) ≤ q →
      P {ω | ¬ ((∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
        η ω '' Icc (sSup {t : ℝ | t ≤ 0 ∧ η ω t ∉ ball 0 (1 : ℝ)}) 0) ∧
        (∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
        η ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ η ω t ∉ ball 0 (1 : ℝ)})))} ≤
      ENNReal.ofReal (C * δ ^ N) := by
  obtain ⟨C, hC⟩ := D.segmentsContainBalls ρ (lt_trans hq hqρ) r hr N
  refine ⟨C, ?_⟩
  intro δ hδ hδq
  apply le_trans ?_ (hC δ hδ)
  apply measure_mono_ae
  filter_upwards [D.spaceFilling, D.areaParam] with ω hspace harea
  intro hbad hsegments
  obtain ⟨φ, hφ0, hη⟩ := harea.1
  have hmem : (ηL ω) ⁻¹' (closedBall (0 : ℂ) 1)ᶜ ∈ cocompact ℝ :=
    hspace.2.1 (isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact
  obtain ⟨K, hK, hKsub⟩ := mem_cocompact.mp hmem
  obtain ⟨a, ha⟩ := hK.bddBelow
  obtain ⟨b, hb⟩ := hK.bddAbove
  have hleft : {t : ℝ | t ≤ 0 ∧ ηL ω t ∉ ball 0 (1 : ℝ)}.Nonempty := by
    refine ⟨min a 0 - 1, by linarith [min_le_right a (0 : ℝ)], ?_⟩
    have hout : min a 0 - 1 ∉ K := by
      intro ht
      have := ha ht
      linarith [min_le_left a (0 : ℝ)]
    exact fun ht => (hKsub hout) (ball_subset_closedBall ht)
  have hright : {t : ℝ | 0 ≤ t ∧ ηL ω t ∉ ball 0 (1 : ℝ)}.Nonempty := by
    refine ⟨max b 0 + 1, by linarith [le_max_right b (0 : ℝ)], ?_⟩
    have hout : max b 0 + 1 ∉ K := by
      intro ht
      have := hb ht
      linarith [le_max_left b (0 : ℝ)]
    exact fun ht => (hKsub hout) (ball_subset_closedBall ht)
  have hw := centered_ball_subset_both_exits_of_segments (ηL ω) hspace.2.2.1
    hq hqρ hρ.le ⟨hδ.1, le_rfl⟩ hδq hsegments hleft hright
  have hfun : (η ω : ℝ → ℂ) = (ηL ω : ℝ → ℂ) ∘ φ := funext hη
  have htr := rooted_exit_traces_comp_orderIso (ηL ω) (ball 0 (1 : ℝ)) φ hφ0
  apply hbad
  rw [hfun]
  rw [htr.1, htr.2]
  exact hw

end LatticeProb.LQG
