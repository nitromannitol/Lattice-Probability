import LatticeProb.Prob.CorrelatedBMConeTimes

/-! # Gaussian laws of correlated Brownian increments

Each coordinate increment of a two-sided correlated Brownian pair is a
centered Gaussian with variance equal to the elapsed time.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- A coordinate increment is centered Gaussian, also for reversed times and
coincident endpoints. -/
theorem map_coneIncr_eq_gaussianReal {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) (x c : ℝ) :
    μ.map (coneIncr i x c) = gaussianReal 0 (|x - c|).toNNReal := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hG : HasGaussianLaw (coneIncr i x c) μ :=
    hμ.isGaussianProcess.hasGaussianLaw_fun_sub (s := (i, x)) (t := (i, c))
  have hmean : μ[coneIncr i x c] = 0 := by
    change μ[fun ω => lrCoord i x ω - lrCoord i c ω] = 0
    rw [integral_sub (hμ.isGaussianProcess.hasGaussianLaw_eval (i, x)).integrable
      (hμ.isGaussianProcess.hasGaussianLaw_eval (i, c)).integrable,
      hμ.integral_eq_zero, hμ.integral_eq_zero, sub_self]
  have hvar : Var[coneIncr i x c; μ] = |x - c| := by
    rw [← covariance_self hG.aemeasurable, cov_coneIncr hμ]
    simp [lrCov]
  rw [hG.map_eq_gaussianReal, hmean, hvar]

end LatticeProb.CorrelatedBM
