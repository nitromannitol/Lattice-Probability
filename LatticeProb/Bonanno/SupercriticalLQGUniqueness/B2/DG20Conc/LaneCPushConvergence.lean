/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPushConvergence at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPushDensity

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.LFPP

theorem laneC_push_deriv_tendsto {γ : ℝ → ℂ} {t : ℝ}
    (hγ : DifferentiableAt ℝ γ t) :
    Tendsto (fun n => deriv (laneCInwardPush (laneCPushSequence n) ∘ γ) t)
      atTop (nhds (deriv γ t)) := by
  have hp : Tendsto (fun n : ℕ => (laneCPushSequence n, γ t)) atTop
      (nhds (0, γ t)) := laneC_push_sequence_tendsto.prodMk_nhds tendsto_const_nhds
  have hF : Tendsto (fun n => fderiv ℝ (laneCInwardPush (laneCPushSequence n)) (γ t))
      atTop (nhds (fderiv ℝ (laneCInwardPush 0) (γ t))) := by
    exact (laneC_inwardPush_fderiv_continuous.tendsto (0, γ t)).comp hp
  have hzero : fderiv ℝ (laneCInwardPush 0) (γ t) =
      ContinuousLinearMap.id ℝ ℂ := by
    have heq : laneCInwardPush 0 = id := funext laneC_inwardPush_zero
    rw [heq]
    exact fderiv_id
  have h := ((ContinuousLinearMap.apply ℝ ℂ (deriv γ t)).continuous.tendsto
    (fderiv ℝ (laneCInwardPush 0) (γ t))).comp hF
  rw [hzero] at h
  have h' : Tendsto (fun n =>
      (fderiv ℝ (laneCInwardPush (laneCPushSequence n)) (γ t)) (deriv γ t))
      atTop (nhds (deriv γ t)) := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.id_apply] using h
  simpa only [laneC_inwardPush_deriv_comp hγ] using h'

theorem laneC_push_density_tendsto {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) {γ : ℝ → ℂ} {t : ℝ}
    (hγ : DifferentiableAt ℝ γ t) :
    Tendsto (fun n => lenDens ξ f (laneCInwardPush (laneCPushSequence n) ∘ γ) t)
      atTop (nhds (lenDens ξ f γ t)) := by
  have hz : Tendsto (fun n => laneCInwardPush (laneCPushSequence n) (γ t)) atTop
      (nhds (γ t)) := (laneC_inwardPush_tendsto (γ t)).comp laneC_push_sequence_tendsto
  have hweight : Tendsto (fun n => Real.exp (ξ * f
      (laneCInwardPush (laneCPushSequence n) (γ t)))) atTop
      (nhds (Real.exp (ξ * f (γ t)))) :=
    Real.continuous_exp.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul (hf.continuousAt.tendsto.comp hz))
  unfold lenDens
  exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (hweight.mul (laneC_push_deriv_tendsto hγ).norm)

end SupercriticalLQGUniqueness.B2.DG20Conc
