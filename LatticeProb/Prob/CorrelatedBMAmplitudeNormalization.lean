import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.TransferScaling
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianLaw

/-! # Amplitude normalization of a Gaussian path pair -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- Scale both coordinates of a continuous path, keeping its time parameter. -/
def amplitudeScale (c : ℝ) (ω : Path2) : Path2 :=
  ⟨fun t => c • ω t, by fun_prop⟩

/-- Amplitude scaling is measurable on continuous path space. -/
theorem measurable_amplitudeScale (c : ℝ) : Measurable (amplitudeScale c) := by
  apply ContinuousMap.measurable_iff_eval.2
  intro t
  change Measurable (fun ω : Path2 => c • ω t)
  apply Measurable.prodMk
  · simpa using (measurable_fst.comp (ContinuousMap.measurable_eval t)).const_mul c
  · simpa using (measurable_snd.comp (ContinuousMap.measurable_eval t)).const_mul c

private def evalCoords (I : Finset (Fin 2 × ℝ)) (ω : Path2) : I → ℝ :=
  fun p => lrCoord p.1.1 p.1.2 ω

private theorem measurable_evalCoords (I : Finset (Fin 2 × ℝ)) :
    Measurable (evalCoords I) := by
  apply Measurable.of_eval
  intro p
  exact measurable_lrCoord p.1

/-- A centered Gaussian path pair with common positive standard deviation `σ`
becomes a unit-variance correlated Brownian path law after amplitude scaling. -/
theorem isCorrelatedBM2_map_amplitudeScale_inv
    {γ σ : ℝ} {μ : Measure Path2} [IsProbabilityMeasure μ] (hσ : 0 < σ)
    (hG : IsGaussianProcess (fun p : Fin 2 × ℝ => lrCoord p.1 p.2) μ)
    (hmean : ∀ i t, ∫ ω, lrCoord i t ω ∂μ = 0)
    (hcov : ∀ i j s t, cov[lrCoord i s, lrCoord j t; μ] =
      σ * σ * (lrCov γ i j * twoSidedMin s t)) :
    IsCorrelatedBM2 γ (μ.map (amplitudeScale σ⁻¹)) := by
  let F := amplitudeScale σ⁻¹
  have hF : Measurable F := measurable_amplitudeScale _
  have hcoord (i : Fin 2) (t : ℝ) (ω : Path2) :
      lrCoord i t (F ω) = σ⁻¹ * lrCoord i t ω := by
    fin_cases i <;> simp [F, amplitudeScale, lrCoord]
  have hscaled : IsGaussianProcess
      (fun p : Fin 2 × ℝ => fun ω => σ⁻¹ * lrCoord p.1 p.2 ω) μ :=
    hG.smul (fun _ => σ⁻¹)
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · refine ⟨fun I => ?_⟩
    refine ⟨(measurable_evalCoords I).aemeasurable, ?_⟩
    change IsGaussian ((μ.map F).map (evalCoords I))
    rw [AEMeasurable.map_map_of_aemeasurable
      (measurable_evalCoords I).aemeasurable hF.aemeasurable]
    have heq : evalCoords I ∘ F =
        (fun ω => I.restrict (fun p => σ⁻¹ * lrCoord p.1 p.2 ω)) := by
      funext ω p
      exact hcoord p.1.1 p.1.2 ω
    rw [heq]
    exact (hscaled.hasGaussianLaw I).isGaussian_map
  · intro i t
    rw [integral_map hF.aemeasurable (measurable_lrCoord (i, t)).aestronglyMeasurable]
    change ∫ ω, lrCoord i t (F ω) ∂μ = 0
    simp only [hcoord, integral_const_mul, hmean, mul_zero]
  · intro i j s t
    rw [covariance_map (measurable_lrCoord (i, s)).aestronglyMeasurable
      (measurable_lrCoord (j, t)).aestronglyMeasurable hF.aemeasurable]
    change cov[lrCoord i s ∘ F, lrCoord j t ∘ F; μ] = _
    rw [show lrCoord i s ∘ F = fun ω => σ⁻¹ * lrCoord i s ω by
        funext ω; exact hcoord i s ω,
      show lrCoord j t ∘ F = fun ω => σ⁻¹ * lrCoord j t ω by
        funext ω; exact hcoord j t ω,
      covariance_const_mul_left, covariance_const_mul_right, hcov]
    field_simp

end LatticeProb.CorrelatedBM
