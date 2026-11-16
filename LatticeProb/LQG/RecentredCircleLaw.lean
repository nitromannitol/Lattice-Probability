import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.CircleCov

/-! # Gaussian law of a recentred circle average -/

open MeasureTheory ProbabilityTheory
open MatedCRTHarmonic.GMCFacts

namespace LatticeProb.LQG

/-- A circle average recentred by a containing circle has the logarithmic Gaussian law. -/
theorem hasLaw_recentred_circle {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (hrε : r ≤ ε / 2)
    {z w : ℂ} (hw : ‖w - z‖ ≤ ε / 2) :
    HasLaw (fun ω => H r w ω - H ε z ω)
      (gaussianReal 0 (Real.log (ε / r)).toNNReal) P := by
  have := hH.isProbabilityMeasure
  have hG : HasGaussianLaw (fun ω => H r w ω - H ε z ω) P :=
    hH.isGaussianProcess.hasGaussianLaw_fun_sub (s := (⟨r, hr⟩, w)) (t := (⟨ε, hε⟩, z))
  have hmean : ∫ ω, (H r w ω - H ε z ω) ∂P = 0 := by
    rw [integral_sub ((memLp_two_coord hH hr w).integrable (by norm_num)) ((memLp_two_coord hH hε z).integrable (by norm_num)),
      hH.integral_eq_zero r hr w, hH.integral_eq_zero ε hε z, sub_self]
  have hvar : Var[fun ω => H r w ω - H ε z ω; P] = Real.log (ε / r) := by
    rw [← covariance_self hG.aemeasurable, cov_recentred_self hH hε hr hrε hw,
      Real.log_div hε.ne' hr.ne']
  exact ⟨hG.aemeasurable, by rw [hG.map_eq_gaussianReal, hmean, hvar]⟩

end LatticeProb.LQG
