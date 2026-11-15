import LatticeProb.LQG.GMCDilationField

/-! # Bounds for singular approximants below the regularization scale -/

open MeasureTheory Set Metric

namespace LatticeProb.LQG

open LatticeProb.Gauss

/-- On a ball contained in a circle of radius `r`, the logarithmic insertion
has constant circle average. An upper bound on the field gives a mass bound. -/
theorem lqgApprox_singular_ball_le_of_circle_le
    {γ α r R A : ℝ} (hγ : 0 ≤ γ) (hr : 0 < r) (hR : R ≤ r)
    (h : ℝ → ℂ → ℝ) (hh : ∀ z ∈ ball (0 : ℂ) R, h r z ≤ A) :
    lqgApprox γ (fieldCircleAverage α h) r (ball 0 R) ≤
      ENNReal.ofReal (r ^ (γ ^ 2 / 2) * Real.exp (γ * (A - α * Real.log r))) *
        volume (ball (0 : ℂ) R) := by
  rw [lqgApprox, withDensity_apply _ measurableSet_ball]
  calc
    (∫⁻ z in ball (0 : ℂ) R,
      ENNReal.ofReal (r ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCircleAverage α h r z))) ≤
        ∫⁻ _z in ball (0 : ℂ) R,
          ENNReal.ofReal (r ^ (γ ^ 2 / 2) * Real.exp (γ * (A - α * Real.log r))) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      have hz' : ‖z‖ ≤ r := by
        have : ‖z‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hz
        exact (le_of_lt this).trans hR
      have hc : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) z r = Real.log r := by
        simpa only [sub_zero, max_eq_left hz'] using
          circleAverage_log_norm_sub_eq_log_max hr z 0
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hr.le _)
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hγ
      simpa only [fieldCircleAverage, hc] using sub_le_sub_right (hh z hz) (α * Real.log r)
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

/-- The same bound at dyadic radii whenever the ball index dominates the
regularization index. -/
theorem lqgApprox_singular_dyadic_ball_le_of_circle_le
    {γ α A : ℝ} (hγ : 0 ≤ γ) (h : ℝ → ℂ → ℝ) {J k : ℕ} (hkJ : k ≤ J)
    (hh : ∀ z ∈ ball (0 : ℂ) (dyadicScale J), h (dyadicScale k) z ≤ A) :
    lqgApprox γ (fieldCircleAverage α h) (dyadicScale k) (ball 0 (dyadicScale J)) ≤
      ENNReal.ofReal ((dyadicScale k) ^ (γ ^ 2 / 2) *
        Real.exp (γ * (A - α * Real.log (dyadicScale k)))) *
        volume (ball (0 : ℂ) (dyadicScale J)) := by
  apply lqgApprox_singular_ball_le_of_circle_le hγ (by unfold dyadicScale; positivity) _ h hh
  unfold dyadicScale
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hkJ

end LatticeProb.LQG
