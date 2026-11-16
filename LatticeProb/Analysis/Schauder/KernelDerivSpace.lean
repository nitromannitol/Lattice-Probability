import LatticeProb.Analysis.Schauder.KernelDef

/-!
# Space derivatives of the Gaussian heat kernel

The heat kernel `p_t(x) = (4πt)^{-d/2} exp(-‖x‖²/(4t))` on `ℝ^d` is smooth in `x`, and its first
two space derivatives are explicit Gaussian-weighted polynomials:
`∂_v p_t(x) = -(⟪x, v⟫ / (2t)) p_t(x)` and
`∂_u ∂_v p_t(x) = (⟪x, u⟫⟪x, v⟫ / (4t²) - ⟪u, v⟫ / (2t)) p_t(x)`.
These are the formulas behind the `L¹` bounds on the derivatives of `p_t`.
-/

namespace LatticeProb.Analysis.Schauder

open Real

open scoped InnerProductSpace

noncomputable section

variable {d : ℕ}

/-- The heat kernel is smooth in the space variable, at every time. -/
theorem contDiff_heatKernel (t : ℝ) : ContDiff ℝ ⊤ (heatKernel d t) := by
  have h : ContDiff ℝ ⊤ fun x : Euc d => -‖x‖ ^ 2 / (4 * t) :=
    ((contDiff_norm_sq ℝ).neg).div_const _
  exact contDiff_const.mul (Real.contDiff_exp.comp h)

/-- The `HasFDerivAt` form of the first space derivative of the heat kernel. -/
theorem hasFDerivAt_heatKernel {t : ℝ} (ht : 0 < t) (x : Euc d) :
    HasFDerivAt (heatKernel d t) (-(heatKernel d t x / (2 * t)) • innerSL ℝ x) x := by
  have h1 : HasFDerivAt (fun y : Euc d => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h2 := ((h1.const_mul (-(4 * t)⁻¹)).exp).const_mul ((4 * π * t) ^ (-(d : ℝ) / 2))
  refine (h2.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => heatKernel_eq t y)).congr_fderiv ?_
  ext v
  simp only [heatKernel_eq, smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  field_simp
  ring

/-- The first space derivative of the heat kernel in the direction `v` is
`-(⟪x, v⟫ / (2t)) p_t(x)`. -/
theorem fderiv_heatKernel_apply {t : ℝ} (ht : 0 < t) (x v : Euc d) :
    fderiv ℝ (heatKernel d t) x v = -(⟪x, v⟫_ℝ / (2 * t)) * heatKernel d t x := by
  rw [(hasFDerivAt_heatKernel ht x).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

/-- The second space derivative of the heat kernel, in the form `∂_u (∂_v p_t)`, is
`(⟪x, u⟫⟪x, v⟫ / (4t²) - ⟪u, v⟫ / (2t)) p_t(x)`. -/
theorem fderiv_fderiv_heatKernel_apply {t : ℝ} (ht : 0 < t) (x u v : Euc d) :
    fderiv ℝ (fun y => fderiv ℝ (heatKernel d t) y v) x u =
      (⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ / (4 * t ^ 2) - ⟪u, v⟫_ℝ / (2 * t)) * heatKernel d t x := by
  have hfun : (fun y => fderiv ℝ (heatKernel d t) y v) =
      fun y => (-(2 * t)⁻¹ * innerSL ℝ v y) * heatKernel d t y := by
    funext y
    rw [fderiv_heatKernel_apply ht, innerSL_apply_apply, real_inner_comm]
    ring
  have hin := ((innerSL ℝ v).hasFDerivAt (x := x)).const_mul (-(2 * t)⁻¹)
  have hprod := hin.fun_mul (hasFDerivAt_heatKernel ht x)
  rw [hfun, hprod.fderiv]
  simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [real_inner_comm v x, real_inner_comm v u]
  field_simp
  ring

/-- The second Fréchet derivative of the heat kernel, as the iterated derivative evaluated on
`![u, v]`, is `(⟪x, u⟫⟪x, v⟫ / (4t²) - ⟪u, v⟫ / (2t)) p_t(x)`. -/
theorem iteratedFDeriv_two_heatKernel_apply {t : ℝ} (ht : 0 < t) (x u v : Euc d) :
    iteratedFDeriv ℝ 2 (heatKernel d t) x ![u, v] =
      (⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ / (4 * t ^ 2) - ⟪u, v⟫_ℝ / (2 * t)) * heatKernel d t x := by
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (heatKernel d t)) x :=
    (((contDiff_heatKernel t).fderiv_right (m := 1) le_top).differentiable
      one_ne_zero).differentiableAt
  rw [← fderiv_fderiv_heatKernel_apply ht, iteratedFDeriv_two_apply,
    fderiv_clm_apply hdiff (differentiableAt_const v)]
  simp

end

end LatticeProb.Analysis.Schauder
