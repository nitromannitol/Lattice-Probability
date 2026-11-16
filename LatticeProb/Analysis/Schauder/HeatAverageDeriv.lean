import LatticeProb.Analysis.Schauder.KernelDerivTime
import LatticeProb.Analysis.Schauder.KernelIntegral
import LatticeProb.Analysis.Schauder.GaussDom

/-!
# Differentiating a heat-kernel average in time

For a bounded continuous function `g` on `ℝ^d`, the heat-kernel average
`t ↦ ∫ p_t(y) g(x - y) dy` is differentiable at every positive time `t₀`, and its derivative is
obtained by differentiating the kernel under the integral sign. The domination required by the
differentiation lemma comes from the pointwise Gaussian bound on the time derivative of `p_t`,
uniform for `t ∈ (t₀/2, 3t₀/2)`, which reduces (through `GaussDom`) to the integrable Gaussian
`exp(-(6t₀)⁻¹ ‖y‖²)` with polynomial prefactors absorbed into half of it.
-/

namespace LatticeProb.Analysis.Schauder

open Real MeasureTheory Filter Topology

noncomputable section

variable {d : ℕ}

/-- The heat kernel is continuous in space. -/
private theorem continuous_heatKernel_space (t : ℝ) : Continuous (heatKernel d t) := by
  unfold heatKernel
  fun_prop

/-- The Gaussian `exp(-(6t₀)⁻¹ ‖y‖²)` dominating the heat kernel for times near `t₀`. -/
private theorem heatKernel_le_gauss {t₀ t : ℝ} (ht₀ : 0 < t₀)
    (ht : t ∈ Set.Ioo (t₀ / 2) (3 * t₀ / 2)) (y : Euc d) :
    heatKernel d t y ≤
      (2 * π * t₀) ^ (-(d : ℝ) / 2) * Real.exp (-(6 * t₀)⁻¹ * ‖y‖ ^ 2) := by
  obtain ⟨hlo, hhi⟩ := ht
  have htpos : 0 < t := by linarith
  have h2 : 0 < 2 * π * t₀ := by positivity
  have h1 : (4 * π * t) ^ (-(d : ℝ) / 2) ≤ (2 * π * t₀) ^ (-(d : ℝ) / 2) := by
    refine Real.rpow_le_rpow_of_nonpos h2 ?_ ?_
    · nlinarith [Real.pi_pos]
    · have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
  have h3 : Real.exp (-‖y‖ ^ 2 / (4 * t)) ≤ Real.exp (-(6 * t₀)⁻¹ * ‖y‖ ^ 2) := by
    refine Real.exp_le_exp.mpr ?_
    have h4 : (6 * t₀)⁻¹ ≤ (4 * t)⁻¹ := by
      apply inv_anti₀ (by positivity)
      linarith
    have h5 : -‖y‖ ^ 2 / (4 * t) = -(4 * t)⁻¹ * ‖y‖ ^ 2 := by
      rw [div_eq_mul_inv]; ring
    rw [h5]
    nlinarith [sq_nonneg ‖y‖]
  unfold heatKernel
  exact mul_le_mul h1 h3 (Real.exp_pos _).le (Real.rpow_nonneg h2.le _)

/-- The coefficient of the time derivative of the heat kernel is bounded by `d/t₀ + ‖y‖²/t₀²`
for times in `(t₀/2, 3t₀/2)`. -/
private theorem abs_coeff_le {t₀ t : ℝ} (ht₀ : 0 < t₀) (ht : t ∈ Set.Ioo (t₀ / 2) (3 * t₀ / 2))
    (y : Euc d) :
    |-(d : ℝ) / (2 * t) + ‖y‖ ^ 2 / (4 * t ^ 2)| ≤ (d : ℝ) / t₀ + ‖y‖ ^ 2 / t₀ ^ 2 := by
  obtain ⟨hlo, hhi⟩ := ht
  have htpos : 0 < t := by linarith
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hy : 0 ≤ ‖y‖ ^ 2 := sq_nonneg _
  have e1 : (d : ℝ) / (2 * t) ≤ (d : ℝ) / t₀ := by
    apply div_le_div_of_nonneg_left hd ht₀
    linarith
  have e2 : ‖y‖ ^ 2 / (4 * t ^ 2) ≤ ‖y‖ ^ 2 / t₀ ^ 2 := by
    apply div_le_div_of_nonneg_left hy (by positivity)
    nlinarith
  have e3 : 0 ≤ (d : ℝ) / (2 * t) := by positivity
  have e4 : 0 ≤ ‖y‖ ^ 2 / (4 * t ^ 2) := by positivity
  have e5 : -(d : ℝ) / (2 * t) = -((d : ℝ) / (2 * t)) := by ring
  rw [e5]
  rw [abs_le]
  constructor <;> linarith

/-- The pointwise bound on the time derivative of the heat kernel, uniform for times in
`(t₀/2, 3t₀/2)`, in the form of an explicit Gaussian with polynomial prefactors. -/
private theorem abs_deriv_heatKernel_le {t₀ t : ℝ} (ht₀ : 0 < t₀)
    (ht : t ∈ Set.Ioo (t₀ / 2) (3 * t₀ / 2)) (y : Euc d) :
    |(-(d : ℝ) / (2 * t) + ‖y‖ ^ 2 / (4 * t ^ 2)) * heatKernel d t y| ≤
      (2 * π * t₀) ^ (-(d : ℝ) / 2) *
        (((d : ℝ) / t₀) * Real.exp (-(6 * t₀)⁻¹ * ‖y‖ ^ 2) +
          (t₀ ^ 2)⁻¹ * (‖y‖ ^ 2 * Real.exp (-(6 * t₀)⁻¹ * ‖y‖ ^ 2))) := by
  have htpos : 0 < t := by linarith [ht.1]
  rw [abs_mul, abs_of_nonneg (heatKernel_nonneg htpos y)]
  have hc := abs_coeff_le ht₀ ht y
  have hk := heatKernel_le_gauss ht₀ ht y
  calc |-(d : ℝ) / (2 * t) + ‖y‖ ^ 2 / (4 * t ^ 2)| * heatKernel d t y
      ≤ ((d : ℝ) / t₀ + ‖y‖ ^ 2 / t₀ ^ 2) *
        ((2 * π * t₀) ^ (-(d : ℝ) / 2) * Real.exp (-(6 * t₀)⁻¹ * ‖y‖ ^ 2)) :=
        mul_le_mul hc hk (heatKernel_nonneg htpos y) (by positivity)
    _ = (2 * π * t₀) ^ (-(d : ℝ) / 2) *
        (((d : ℝ) / t₀) * Real.exp (-(6 * t₀)⁻¹ * ‖y‖ ^ 2) +
          (t₀ ^ 2)⁻¹ * (‖y‖ ^ 2 * Real.exp (-(6 * t₀)⁻¹ * ‖y‖ ^ 2))) := by
        ring

/-- The integrable dominating function: a Gaussian `exp(-(6t₀)⁻¹ ‖y‖²)` times a polynomial
`d/t₀ + ‖y‖²/t₀²`, is integrable. -/
private theorem integrable_gauss_poly {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Integrable (fun y : Euc d =>
      ((d : ℝ) / t₀) * Real.exp (-(6 * t₀)⁻¹ * ‖y‖ ^ 2) +
        (t₀ ^ 2)⁻¹ * (‖y‖ ^ 2 * Real.exp (-(6 * t₀)⁻¹ * ‖y‖ ^ 2))) := by
  have hb : 0 < (6 * t₀)⁻¹ := inv_pos.mpr (by positivity)
  have hb2 : 0 < (6 * t₀)⁻¹ / 2 := by positivity
  have hE : Integrable (fun y : Euc d => Real.exp (-(6 * t₀)⁻¹ * ‖y‖ ^ 2)) :=
    integrable_exp_neg_mul_sq_norm_euc hb
  have hE2 : Integrable (fun y : Euc d => Real.exp (-((6 * t₀)⁻¹ / 2) * ‖y‖ ^ 2)) :=
    integrable_exp_neg_mul_sq_norm_euc hb2
  have hP : Integrable (fun y : Euc d => ‖y‖ ^ 2 * Real.exp (-(6 * t₀)⁻¹ * ‖y‖ ^ 2)) := by
    refine Integrable.mono' (hE2.const_mul ((6 * t₀)⁻¹)⁻¹) ?_ ?_
    · exact (by fun_prop : Continuous fun y : Euc d =>
        ‖y‖ ^ 2 * Real.exp (-(6 * t₀)⁻¹ * ‖y‖ ^ 2)).aestronglyMeasurable
    · refine Eventually.of_forall fun y => ?_
      rw [Real.norm_of_nonneg (by positivity)]
      exact norm_sq_mul_exp_neg_le hb y
  exact (hE.const_mul _).add (hP.const_mul _)

/-- Differentiation in time under the integral of a heat-kernel average of a bounded continuous
function. -/
theorem hasDerivAt_integral_heatKernel_mul {g : Euc d → ℝ} (hgc : Continuous g) {A : ℝ}
    (hgA : ∀ y, |g y| ≤ A) (x : Euc d) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    HasDerivAt (fun t => ∫ y, heatKernel d t y * g (x - y))
      (∫ y, ((-(d : ℝ) / (2 * t₀) + ‖y‖ ^ 2 / (4 * t₀ ^ 2)) * heatKernel d t₀ y) * g (x - y))
      t₀ := by
  have hgx : Continuous fun y : Euc d => g (x - y) := hgc.comp (continuous_const.sub continuous_id)
  have hs : Set.Ioo (t₀ / 2) (3 * t₀ / 2) ∈ 𝓝 t₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hmeas : ∀ t, AEStronglyMeasurable (fun y : Euc d => heatKernel d t y * g (x - y)) volume :=
    fun t => ((continuous_heatKernel_space t).mul hgx).aestronglyMeasurable
  have hint : Integrable (fun y : Euc d => heatKernel d t₀ y * g (x - y)) :=
    (integrable_heatKernel ht₀).mul_bdd hgx.aestronglyMeasurable
      (Eventually.of_forall fun y => by simpa using hgA (x - y))
  have hF'meas : AEStronglyMeasurable
      (fun y : Euc d => ((-(d : ℝ) / (2 * t₀) + ‖y‖ ^ 2 / (4 * t₀ ^ 2)) * heatKernel d t₀ y) *
        g (x - y)) volume := by
    have := continuous_heatKernel_space (d := d) t₀
    exact (by fun_prop : Continuous fun y : Euc d =>
      ((-(d : ℝ) / (2 * t₀) + ‖y‖ ^ 2 / (4 * t₀ ^ 2)) * heatKernel d t₀ y) *
        g (x - y)).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t y => heatKernel d t y * g (x - y))
    (F' := fun t y => ((-(d : ℝ) / (2 * t) + ‖y‖ ^ 2 / (4 * t ^ 2)) * heatKernel d t y) *
      g (x - y))
    (bound := fun y => |A| * ((2 * π * t₀) ^ (-(d : ℝ) / 2) *
      (((d : ℝ) / t₀) * Real.exp (-(6 * t₀)⁻¹ * ‖y‖ ^ 2) +
        (t₀ ^ 2)⁻¹ * (‖y‖ ^ 2 * Real.exp (-(6 * t₀)⁻¹ * ‖y‖ ^ 2)))))
    hs (Eventually.of_forall hmeas) hint hF'meas ?_ ?_ ?_).2
  · refine Eventually.of_forall fun y t ht => ?_
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul (le_trans (hgA (x - y)) (le_abs_self A))
      (abs_deriv_heatKernel_le ht₀ ht y) (abs_nonneg _) (abs_nonneg _)
  · have hmul := (integrable_gauss_poly (d := d) ht₀).const_mul ((2 * π * t₀) ^ (-(d : ℝ) / 2))
    exact hmul.const_mul |A|
  · refine Eventually.of_forall fun y t ht => ?_
    exact (hasDerivAt_heatKernel_time (by linarith [ht.1]) y).mul_const (g (x - y))

end

end LatticeProb.Analysis.Schauder
