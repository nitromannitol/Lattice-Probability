import LatticeProb.Analysis.Schauder.Continuum

/-!
# The Gaussian heat kernel on `ℝ^d`

The heat kernel `p_t(x) = (4πt)^{-d/2} exp(-‖x‖²/(4t))` of `∂_t = Δ` on `ℝ^d`, at positive times.
It is the only kernel in the heat-semigroup proof of the Hessian bound for the Dirichlet inverse,
which replaces the interior Schauder estimate (GT01, Theorem 4.6) in the two-scale expansion: every
estimate there is an `L¹` bound for a derivative of `p_t`, reduced by pointwise domination to the
Gaussian integral `∫ exp(-b‖x‖²) = (π/b)^{d/2}`.

This module fixes the definition, its sign and its splitting `p_t = 2^{d/2} exp(-‖x‖²/(8t)) p_{2t}`;
its integral, derivatives, heat equation and `L¹` bounds are proved in the sibling modules of
`LatticeProb.Analysis.Schauder`.
-/

namespace LatticeProb.Analysis.Schauder

open Real

noncomputable section

variable {d : ℕ}

/-- The Gaussian heat kernel `(4πt)^{-d/2} exp(-‖x‖²/(4t))` on `ℝ^d`, used at times `t > 0`. -/
def heatKernel (d : ℕ) (t : ℝ) (x : Euc d) : ℝ :=
  (4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))

/-- The heat kernel is positive at positive times. -/
theorem heatKernel_pos {t : ℝ} (ht : 0 < t) (x : Euc d) : 0 < heatKernel d t x := by
  unfold heatKernel
  have h : 0 < 4 * π * t := by positivity
  exact mul_pos (Real.rpow_pos_of_pos h _) (Real.exp_pos _)

/-- The heat kernel is nonnegative at positive times. -/
theorem heatKernel_nonneg {t : ℝ} (ht : 0 < t) (x : Euc d) : 0 ≤ heatKernel d t x :=
  (heatKernel_pos ht x).le

/-- The heat kernel is the Gaussian `exp(-b‖x‖²)` with `b = (4t)⁻¹`, times the normalising
constant `(4πt)^{-d/2}`. -/
theorem heatKernel_eq (t : ℝ) (x : Euc d) :
    heatKernel d t x = (4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-(4 * t)⁻¹ * ‖x‖ ^ 2) := by
  unfold heatKernel
  congr 2
  ring

/-- The heat kernel at time `t` is the heat kernel at time `2t`, times the Gaussian:
`p_t(y) = 2^{d/2} exp(-‖y‖²/(8t)) p_{2t}(y)`. -/
theorem heatKernel_eq_two_pow_mul_exp_mul_heatKernel_two_mul {t : ℝ} (ht : 0 < t) (y : Euc d) :
    heatKernel d t y =
      2 ^ ((d : ℝ) / 2) * Real.exp (-(‖y‖ ^ 2 / t / 8)) * heatKernel d (2 * t) y := by
  unfold heatKernel
  have hp : 0 < 4 * π * t := by positivity
  have hc : (4 * π * (2 * t)) ^ (-(d : ℝ) / 2) =
      2 ^ (-((d : ℝ) / 2)) * (4 * π * t) ^ (-(d : ℝ) / 2) := by
    rw [show 4 * π * (2 * t) = 2 * (4 * π * t) by ring, Real.mul_rpow (by norm_num) hp.le,
      neg_div]
  have he : Real.exp (-‖y‖ ^ 2 / (4 * t)) =
      Real.exp (-(‖y‖ ^ 2 / t / 8)) * Real.exp (-‖y‖ ^ 2 / (4 * (2 * t))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have h2 : (2 : ℝ) ^ ((d : ℝ) / 2) ≠ 0 := by positivity
  rw [he, hc, Real.rpow_neg (by norm_num)]
  field_simp

end

end LatticeProb.Analysis.Schauder
