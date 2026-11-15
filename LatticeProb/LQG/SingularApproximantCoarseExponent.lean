import LatticeProb.LQG.SingularApproximantCoarseDensity

/-! # Explicit dyadic mass bounds below the regularization scale -/

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss

/-- A spatial upper bound on the circle average gives the explicit dyadic
mass exponent for a ball no larger than the regularization scale. -/
theorem lqgApprox_singular_dyadic_ball_le_exp
    {γ α δ C : ℝ} (hγ : 0 ≤ γ) (h : ℝ → ℂ → ℝ) {J k : ℕ} (hkJ : k ≤ J)
    (hh : ∀ z ∈ ball (0 : ℂ) (dyadicScale J),
      h (dyadicScale k) z ≤ C + (2 + δ) * Real.log (dyadicScale k)⁻¹) :
    lqgApprox γ (fieldCircleAverage α h) (dyadicScale k) (ball 0 (dyadicScale J)) ≤
      ENNReal.ofReal (Real.pi * Real.exp (γ * C) *
        Real.exp (Real.log 2 * ((γ * (2 + δ) + γ * α - γ ^ 2 / 2) * k - 2 * J))) := by
  have hbound := lqgApprox_singular_dyadic_ball_le_of_circle_le (α := α) hγ h hkJ hh
  have hkpos : 0 < dyadicScale k := by unfold dyadicScale; positivity
  have hJpos : 0 < dyadicScale J := by unfold dyadicScale; positivity
  have hklog : Real.log (dyadicScale k) = -(k : ℝ) * Real.log 2 := by
    rw [dyadicScale, Real.log_pow, Real.log_inv]
    ring
  have hJlog : Real.log (dyadicScale J) = -(J : ℝ) * Real.log 2 := by
    rw [dyadicScale, Real.log_pow, Real.log_inv]
    ring
  have hpi : (↑NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  rw [Complex.volume_ball, hpi,
    ← ENNReal.ofReal_pow hJpos.le, ← ENNReal.ofReal_mul (sq_nonneg _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hkpos.le _) (Real.exp_pos _).le)] at hbound
  refine hbound.trans ?_
  apply le_of_eq
  congr 1
  rw [Real.rpow_def_of_pos hkpos, Real.log_inv, hklog,
    show dyadicScale J ^ 2 = Real.exp (2 * Real.log (dyadicScale J)) by
      rw [mul_comm, Real.exp_mul, Real.exp_log hJpos, Real.rpow_two], hJlog]
  conv_lhs => rw [← mul_assoc, ← Real.exp_add]
  conv_rhs => rw [mul_assoc, ← Real.exp_add]
  rw [← Real.exp_add, mul_comm (Real.exp _) Real.pi]
  congr 2
  ring

end LatticeProb.LQG
