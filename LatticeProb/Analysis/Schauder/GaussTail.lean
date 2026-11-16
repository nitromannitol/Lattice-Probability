import LatticeProb.Analysis.Schauder.KernelDef
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The Gaussian tail of the heat kernel

The mass of the heat kernel `p_t(x) = (4πt)^{-d/2} exp(-‖x‖²/(4t))` outside a ball of fixed radius
`δ > 0` tends to zero as `t → 0⁺`. On `{‖y‖ ≥ δ}` the kernel is dominated by
`exp(-δ²/(8t))` times the Gaussian `(4πt)^{-d/2} exp(-‖y‖²/(8t))`, whose total mass is
`2^{d/2}`, so the tail is at most `2^{d/2} exp(-δ²/(8t))`.
-/

namespace LatticeProb.Analysis.Schauder

open Real MeasureTheory Filter Topology

noncomputable section

variable {d : ℕ}

/-- Outside the ball of radius `δ`, the heat kernel is dominated by `exp(-δ²/(8t))` times the
Gaussian `(4πt)^{-d/2} exp(-‖y‖²/(8t))`. -/
theorem heatKernel_le_exp_mul_gaussian {t δ : ℝ} (ht : 0 < t) {y : Euc d} (hy : δ ≤ ‖y‖)
    (hδ : 0 ≤ δ) :
    heatKernel d t y ≤ Real.exp (-(δ ^ 2 / (8 * t))) *
      ((4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-(8 * t)⁻¹ * ‖y‖ ^ 2)) := by
  have hsq : δ ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ hδ hy 2
  have h8 : 0 < 8 * t := by positivity
  have hdiv : δ ^ 2 / (8 * t) ≤ ‖y‖ ^ 2 / (8 * t) := div_le_div_of_nonneg_right hsq h8.le
  have hexp : Real.exp (-‖y‖ ^ 2 / (4 * t)) ≤
      Real.exp (-(δ ^ 2 / (8 * t))) * Real.exp (-(8 * t)⁻¹ * ‖y‖ ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have e1 : -‖y‖ ^ 2 / (4 * t) = -(‖y‖ ^ 2 / (8 * t)) - ‖y‖ ^ 2 / (8 * t) := by
      field_simp
      ring
    have e2 : -(8 * t)⁻¹ * ‖y‖ ^ 2 = -(‖y‖ ^ 2 / (8 * t)) := by
      field_simp
    rw [e1, e2]
    linarith
  have hc : 0 ≤ (4 * π * t) ^ (-(d : ℝ) / 2) := by positivity
  unfold heatKernel
  calc (4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))
      ≤ (4 * π * t) ^ (-(d : ℝ) / 2) *
        (Real.exp (-(δ ^ 2 / (8 * t))) * Real.exp (-(8 * t)⁻¹ * ‖y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp hc
    _ = _ := by ring

/-- The dominating Gaussian `(4πt)^{-d/2} exp(-‖y‖²/(8t))` is integrable on `ℝ^d` at positive
times. -/
theorem integrable_gaussian_dominant {t : ℝ} (ht : 0 < t) :
    Integrable (fun y : Euc d => (4 * π * t) ^ (-(d : ℝ) / 2) *
      Real.exp (-(8 * t)⁻¹ * ‖y‖ ^ 2)) := by
  have hb : 0 < (8 * t)⁻¹ := inv_pos.mpr (by positivity)
  have hint : Integrable (fun y : Euc d => Real.exp (-(8 * t)⁻¹ * ‖y‖ ^ 2)) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
    exact (Real.rpow_pos_of_pos (div_pos pi_pos hb) _).ne'
  exact hint.const_mul _

/-- The total mass of the dominating Gaussian `(4πt)^{-d/2} exp(-‖y‖²/(8t))` is `2^{d/2}`. -/
theorem integral_gaussian_dominant {t : ℝ} (ht : 0 < t) :
    ∫ y : Euc d, (4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-(8 * t)⁻¹ * ‖y‖ ^ 2) =
      (2 : ℝ) ^ ((d : ℝ) / 2) := by
  have hb : 0 < (8 * t)⁻¹ := inv_pos.mpr (by positivity)
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm hb,
    finrank_euclideanSpace_fin]
  have h4 : 0 ≤ 4 * π * t := by positivity
  have h8 : 0 ≤ π / (8 * t)⁻¹ := by positivity
  have e : π / (8 * t)⁻¹ = (2 : ℝ) * (4 * π * t) := by
    field_simp
    ring
  rw [e, Real.mul_rpow (by norm_num) h4, show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring,
    Real.rpow_neg h4]
  have hp : 0 < (4 * π * t) ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  field_simp

/-- The tail of the heat kernel outside the ball of radius `δ` is at most
`2^{d/2} exp(-δ²/(8t))` at positive times. -/
theorem setIntegral_heatKernel_tail_le {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t) :
    ∫ y in {y : Euc d | δ ≤ ‖y‖}, heatKernel d t y ≤
      Real.exp (-(δ ^ 2 / (8 * t))) * (2 : ℝ) ^ ((d : ℝ) / 2) := by
  have hmeas : MeasurableSet {y : Euc d | δ ≤ ‖y‖} :=
    measurableSet_le measurable_const measurable_norm
  have hg := integrable_gaussian_dominant (d := d) ht
  have hker : Integrable (heatKernel d t) := by
    have hb : 0 < (4 * t)⁻¹ := inv_pos.mpr (by positivity)
    have hint : Integrable (fun y : Euc d => Real.exp (-(4 * t)⁻¹ * ‖y‖ ^ 2)) := by
      refine Integrable.of_integral_ne_zero ?_
      rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
      exact (Real.rpow_pos_of_pos (div_pos pi_pos hb) _).ne'
    have h := hint.const_mul ((4 * π * t) ^ (-(d : ℝ) / 2))
    exact h.congr (Filter.Eventually.of_forall fun x => (heatKernel_eq t x).symm)
  have hdom : Integrable (fun y : Euc d => Real.exp (-(δ ^ 2 / (8 * t))) *
      ((4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-(8 * t)⁻¹ * ‖y‖ ^ 2))) := hg.const_mul _
  calc ∫ y in {y : Euc d | δ ≤ ‖y‖}, heatKernel d t y
      ≤ ∫ y in {y : Euc d | δ ≤ ‖y‖}, Real.exp (-(δ ^ 2 / (8 * t))) *
        ((4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-(8 * t)⁻¹ * ‖y‖ ^ 2)) :=
        setIntegral_mono_on hker.integrableOn hdom.integrableOn hmeas
          fun y hy => heatKernel_le_exp_mul_gaussian ht hy hδ.le
    _ ≤ ∫ y : Euc d, Real.exp (-(δ ^ 2 / (8 * t))) *
        ((4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-(8 * t)⁻¹ * ‖y‖ ^ 2)) :=
        setIntegral_le_integral hdom (Filter.Eventually.of_forall fun y => by positivity)
    _ = Real.exp (-(δ ^ 2 / (8 * t))) * (2 : ℝ) ^ ((d : ℝ) / 2) := by
        rw [integral_const_mul, integral_gaussian_dominant ht]

/-- The mass of the heat kernel outside a ball of fixed radius `δ > 0` tends to zero as
`t → 0⁺`. -/
theorem tendsto_setIntegral_heatKernel_tail {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t => ∫ y in {y : Euc d | δ ≤ ‖y‖}, heatKernel d t y)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => Real.exp (-(δ ^ 2 / (8 * t))) * (2 : ℝ) ^ ((d : ℝ) / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => δ ^ 2 / 8 * t⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
      tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity)
    have h2 : Tendsto (fun t : ℝ => Real.exp (-(δ ^ 2 / (8 * t)))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).congr fun t => ?_
      simp only [Function.comp_apply]
      congr 2
      field_simp
    simpa using h2.mul_const ((2 : ℝ) ^ ((d : ℝ) / 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact setIntegral_nonneg (measurableSet_le measurable_const measurable_norm)
      fun y _ => heatKernel_nonneg ht y
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact setIntegral_heatKernel_tail_le hδ ht

end

end LatticeProb.Analysis.Schauder
