/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPushLength at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPushConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP

theorem laneC_inwardPush_lfppLen_tendsto {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) {γ : ℝ → ℂ} {a b : ℂ}
    (hγ : IsPiecewiseC1Path γ a b)
    (hm : MapsTo γ (Icc (0 : ℝ) 1) laneCDoublePrimeCross) :
    Tendsto (fun n => lfppLen ξ f (laneCInwardPush (laneCPushSequence n) ∘ γ))
      atTop (nhds (lfppLen ξ f γ)) := by
  obtain ⟨B, hB0, hB⟩ := laneC_inwardPush_weight_bound ξ f hf
  obtain ⟨M, hM0, hM⟩ := laneC_inwardPush_fderiv_bound
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  let bound : ℝ → ℝ≥0∞ := fun t =>
    ENNReal.ofReal (B * M) * ENNReal.ofReal ‖deriv γ t‖
  have hdiff : ∀ᵐ t ∂μ, DifferentiableAt ℝ γ t :=
    laneC_piecewise_ae_differentiable hγ
  have hmem : ∀ᵐ t ∂μ, t ∈ Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
  have hbound : ∀ n, (fun t => lenDens ξ f
      (laneCInwardPush (laneCPushSequence n) ∘ γ) t) ≤ᵐ[μ] bound := by
    intro n
    filter_upwards [hdiff, hmem] with t htd htI
    apply laneC_push_density_bound
      (show laneCPushSequence n ∈ Icc (0 : ℝ) (1 / 1000) from
        ⟨(laneC_push_sequence_pos n).le, laneC_push_sequence_le n⟩)
      (hm htI).1 htd
    · intro z hz
      exact hB _ ⟨(laneC_push_sequence_pos n).le, laneC_push_sequence_le n⟩ z hz
    · intro z hz
      exact hM _ ⟨(laneC_push_sequence_pos n).le, laneC_push_sequence_le n⟩ z hz
    · exact hB0
    · exact hM0
  have hfin : ∫⁻ t, bound t ∂μ ≠ ∞ := by
    simp only [bound, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hγ.lintegral_norm_deriv_lt_top.ne
  have hlim : ∀ᵐ t ∂μ, Tendsto (fun n => lenDens ξ f
      (laneCInwardPush (laneCPushSequence n) ∘ γ) t) atTop
      (nhds (lenDens ξ f γ t)) := by
    filter_upwards [hdiff] with t ht
    exact laneC_push_density_tendsto hf ht
  have hmeas : ∀ n, AEMeasurable (fun t => lenDens ξ f
      (laneCInwardPush (laneCPushSequence n) ∘ γ) t) μ := by
    intro n
    have hpath : AEMeasurable (laneCInwardPush (laneCPushSequence n) ∘ γ) μ :=
      ((laneC_inwardPush_continuous _).comp_continuousOn hγ.continuousOn).aemeasurable
        measurableSet_Icc
    have hfield : AEMeasurable (fun t => Real.exp
        (ξ * f ((laneCInwardPush (laneCPushSequence n) ∘ γ) t))) μ := by
      exact Real.measurable_exp.comp_aemeasurable
        ((measurable_const.mul hf.measurable).comp_aemeasurable hpath)
    unfold lenDens
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (hfield.mul ((measurable_deriv _).norm.aemeasurable))
  have h := tendsto_lintegral_of_dominated_convergence'
    (μ := μ) bound hmeas hbound hfin hlim
  simpa only [lfppLen_eq] using h

end SupercriticalLQGUniqueness.B2.DG20Conc
