import LatticeProb.Walk.GMSContainedStepInterpolation
import LatticeProb.Prob.WeakPathWindowContainment
import LatticeProb.Prob.CellConfigWalkMeasurable

/-! # Quenched comparison of step walks and interpolations -/

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set Metric ReflectedGMS ReflectedGMS.GMS
open scoped ENNReal NNReal Topology

namespace LatticeProb.GMSScaledAdjacentJump

/-- For almost every environment, weak convergence of the rescaled interpolated
walk implies compact-window closeness in outer probability to the step walk,
provided that the path law has adjacent steps and unbounded jump times. -/
theorem ae_step_interpolation_close_in_probability
    {μ : Measure GMSSpace} [IsProbabilityMeasure μ]
    (hL : ConnectedAlongLines μ) (hMT : MassTransport μ) (hFE : FiniteExpectation μ) :
    ∀ᵐ H ∂μ, ∀ (p : H.1.cells → Plane), (∀ K, p K ∈ (K.1 : Set Plane)) →
      (∀ K, 0 < H.1.holding K) →
      ∀ (Q : Measure (ℕ → H.1.cells)) [IsProbabilityMeasure Q],
      (∀ᵐ ω ∂Q, H.1.JumpTimesUnbounded ω ∧ ∀ n, H.1.Adj (ω n) (ω (n + 1))) →
      ∀ (ν : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)),
      Tendsto (fun ε : ℝ≥0 => Q.toProbabilityMeasure.map (H.1.interpolatedWalk p ε))
        (𝓝[>] 0) (𝓝 ν) →
      ∀ (T : ℝ≥0) (δ : ℝ), 0 < δ →
      Tendsto (fun ε : ℝ≥0 => Q {ω | ∃ t : ℝ≥0, t ≤ T ∧
        δ < dist (H.1.interpolatedWalk p ε ω t)
          ((ε : ℝ) • p (H.1.walk ω ((t : ℝ) / (ε : ℝ) ^ 2)))})
        (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [ae_scaled_interpolatedPath_dist_walk_lt hL hMT hFE] with H hgeom
  intro p hp hpos Q hQprob hQ ν hlim T δ hδ
  let : IsProbabilityMeasure Q := hQprob
  let : Countable H.1.cells := CellConfigWalk.countable_cells_of_locallyFinite H.2.locallyFinite
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨R, hR⟩ := eventually_measure_path_window_norm_gt_lt hlim T hη
  obtain ⟨ε₀, hε₀, hgeom₀⟩ := hgeom R δ hδ
  have hεsmall : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, (ε : ℝ) < ε₀ :=
    ((NNReal.continuous_coe.continuousAt.tendsto).mono_left nhdsWithin_le_nhds)
      (Iio_mem_nhds hε₀)
  have hεpos : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  filter_upwards [hR, hεsmall, hεpos] with ε hRε hεlt hεpos
  have hm := H.1.aemeasurable_interpolatedWalk hpos p ε (hQ.mono fun _ h => h.1)
  refine le_of_lt (lt_of_le_of_lt ?_ hRε)
  calc
    Q {ω | ∃ t : ℝ≥0, t ≤ T ∧ δ < dist (H.1.interpolatedWalk p ε ω t)
        ((ε : ℝ) • p (H.1.walk ω ((t : ℝ) / (ε : ℝ) ^ 2)))}
        ≤ Q ((H.1.interpolatedWalk p ε) ⁻¹' {f | ∃ t ≤ T, R < ‖f t‖}) := by
          apply measure_mono_ae
          filter_upwards [hQ] with ω hvalid hbad
          obtain ⟨t, ht, hbad⟩ := hbad
          by_contra hnot
          have hcontain : ∀ s, 0 ≤ s → s ≤ (T : ℝ) / (ε : ℝ) ^ 2 →
              (ε : ℝ) • H.1.interpolatedPath p ω s ∈ closedBall (0 : Plane) R := by
            intro s hs hsT
            let u : ℝ≥0 := ⟨s * (ε : ℝ) ^ 2, mul_nonneg hs (sq_nonneg _)⟩
            have huT : u ≤ T := by
              change s * (ε : ℝ) ^ 2 ≤ (T : ℝ)
              exact (le_div_iff₀ (sq_pos_of_pos (by exact_mod_cast hεpos : (0 : ℝ) < ε))).mp hsT
            have hubound : ‖H.1.interpolatedWalk p ε ω u‖ ≤ R := by
              by_contra hn
              exact hnot ⟨u, huT, lt_of_not_ge hn⟩
            rw [H.1.coe_interpolatedWalk hpos hvalid.1] at hubound
            have hεne : (ε : ℝ) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos (by exact_mod_cast hεpos : (0 : ℝ) < ε))
            have hu : (u : ℝ) / (ε : ℝ) ^ 2 = s := by
              dsimp [u]
              exact mul_div_cancel_right₀ s hεne
            change ‖(ε : ℝ) • H.1.interpolatedPath p ω ((u : ℝ) / (ε : ℝ) ^ 2)‖ ≤ R at hubound
            rw [hu] at hubound
            simpa [mem_closedBall, dist_zero_right] using hubound
          have ht0 : 0 ≤ (t : ℝ) / (ε : ℝ) ^ 2 := div_nonneg (by positivity) (sq_nonneg _)
          have htT : (t : ℝ) / (ε : ℝ) ^ 2 ≤ (T : ℝ) / (ε : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right (by exact_mod_cast ht) (sq_nonneg _)
          have hdist := hgeom₀ (ε : ℝ) (by exact_mod_cast hεpos) hεlt p hp ω hpos
            hvalid.1 hvalid.2 _ hcontain _ ht0 htT
          rw [H.1.coe_interpolatedWalk hpos hvalid.1] at hbad
          exact (not_lt_of_ge hdist.le) hbad
    _ ≤ (Q.toProbabilityMeasure.map (H.1.interpolatedWalk p ε) :
        Measure (BouRabeeGwynne.BrownianPath 2)) {f | ∃ t ≤ T, R < ‖f t‖} :=
      Measure.le_map_apply hm _

end LatticeProb.GMSScaledAdjacentJump
end
