import LatticeProb.Analysis.Schauder.KernelDef
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The integral of the Gaussian heat kernel

The heat kernel `p_t(x) = (4πt)^{-d/2} exp(-‖x‖²/(4t))` on `ℝ^d` is integrable and has total mass
one at every positive time. Both facts reduce, through `heatKernel_eq`, to the Gaussian integral
`∫ exp(-b‖x‖²) = (π/b)^{d/2}` of mathlib, with `b = (4t)⁻¹`.
-/

namespace LatticeProb.Analysis.Schauder

open Real MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The Gaussian integral on `ℝ^d`: `∫ exp(-b‖x‖²) dx = (π/b)^{d/2}` for `b > 0`. -/
theorem integral_exp_neg_mul_sq_norm_euc {b : ℝ} (hb : 0 < b) :
    ∫ x : Euc d, Real.exp (-b * ‖x‖ ^ 2) = (π / b) ^ ((d : ℝ) / 2) := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, finrank_euclideanSpace_fin]

/-- The Gaussian `exp(-b‖x‖²)` is integrable on `ℝ^d` for `b > 0`. -/
theorem integrable_exp_neg_mul_sq_norm_euc {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Euc d => Real.exp (-b * ‖x‖ ^ 2)) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_exp_neg_mul_sq_norm_euc hb]
  have h : 0 < π / b := div_pos pi_pos hb
  exact (Real.rpow_pos_of_pos h _).ne'

/-- The heat kernel is integrable on `ℝ^d` at positive times. -/
theorem integrable_heatKernel {t : ℝ} (ht : 0 < t) : Integrable (heatKernel d t) := by
  have hb : 0 < (4 * t)⁻¹ := inv_pos.mpr (by positivity)
  have h :=
    (integrable_exp_neg_mul_sq_norm_euc (d := d) hb).const_mul ((4 * π * t) ^ (-(d : ℝ) / 2))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  exact (heatKernel_eq t x).symm

/-- The heat kernel has total mass one at positive times. -/
theorem integral_heatKernel {t : ℝ} (ht : 0 < t) : ∫ x, heatKernel d t x = 1 := by
  have hb : 0 < (4 * t)⁻¹ := inv_pos.mpr (by positivity)
  have hp : 0 < 4 * π * t := by positivity
  have hfun : heatKernel d t =
      fun x => (4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-(4 * t)⁻¹ * ‖x‖ ^ 2) :=
    funext fun x => heatKernel_eq t x
  have hdiv : π / (4 * t)⁻¹ = 4 * π * t := by
    field_simp
  rw [hfun, integral_const_mul, integral_exp_neg_mul_sq_norm_euc hb, hdiv,
    neg_div, Real.rpow_neg hp.le]
  exact inv_mul_cancel₀ (Real.rpow_pos_of_pos hp _).ne'

end

end LatticeProb.Analysis.Schauder
