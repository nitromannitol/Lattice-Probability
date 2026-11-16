import LatticeProb.Analysis.Schauder.KernelDerivSpace
import LatticeProb.Analysis.Schauder.KernelIntegral
import LatticeProb.Analysis.Schauder.GaussDom
import LatticeProb.Analysis.Schauder.SineCoeff

/-!
# `L¹` bounds for the first two space derivatives of the heat kernel

For `p_t(x) = (4πt)^{-d/2} exp(-‖x‖²/(4t))` on `ℝ^d` and `t > 0`, the directional derivatives
`∂_u p_t` and `∂_w ∂_u p_t` are integrable, with
`∫ |∂_u p_t| ≤ 2^{d/2} ‖u‖ / √t` and `∫ |∂_w ∂_u p_t| ≤ (2^{d/2} + 1) ‖u‖ ‖w‖ / t`.

The derivatives are the explicit Gaussian-weighted polynomials of `KernelDerivSpace.lean`. The
polynomial factors `‖y‖` and `‖y‖²` are absorbed into half of the Gaussian by `GaussDom.lean`, at
the prices `2√t` and `4t`. What remains is `(4πt)^{-d/2} exp(-‖y‖²/(8t))`, whose integral is
`(4πt)^{-d/2} (8πt)^{d/2} = 2^{d/2}`.
-/

namespace LatticeProb.Analysis.Schauder

open Real MeasureTheory

open scoped RealInnerProductSpace

noncomputable section

variable {d : ℕ}

/-- The heat kernel with its Gaussian weakened to half its strength:
`(4πt)^{-d/2} exp(-‖y‖²/(8t))`. It dominates the heat kernel times a polynomial factor. -/
private def halfGauss (d : ℕ) (t : ℝ) (y : Euc d) : ℝ :=
  (4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-(8 * t)⁻¹ * ‖y‖ ^ 2)

/-- The weakened heat kernel is integrable at positive times. -/
private theorem integrable_halfGauss {t : ℝ} (ht : 0 < t) : Integrable (halfGauss d t) := by
  have hb : 0 < (8 * t)⁻¹ := by positivity
  exact (integrable_exp_neg_mul_sq_norm_euc (d := d) hb).const_mul _

/-- The weakened heat kernel has total mass `2^{d/2}`. -/
private theorem integral_halfGauss {t : ℝ} (ht : 0 < t) :
    ∫ y, halfGauss d t y = 2 ^ ((d : ℝ) / 2) := by
  unfold halfGauss
  have hb : 0 < (8 * t)⁻¹ := by positivity
  have hp : 0 < 4 * π * t := by positivity
  have hq : 0 < 8 * π * t := by positivity
  have h1 : π / (8 * t)⁻¹ = 8 * π * t := by field_simp
  rw [integral_const_mul, integral_exp_neg_mul_sq_norm_euc hb, h1, neg_div,
    Real.rpow_neg hp.le, ← div_eq_inv_mul, ← Real.div_rpow hq.le hp.le]
  have h2 : 8 * π * t / (4 * π * t) = 2 := by
    field_simp
    norm_num
  rw [h2]

/-- The factor `‖y‖` is absorbed by the heat kernel at the price `2√t`, at half the Gaussian
strength. -/
private theorem norm_mul_heatKernel_le {t : ℝ} (ht : 0 < t) (y : Euc d) :
    ‖y‖ * heatKernel d t y ≤ 2 * Real.sqrt t * halfGauss d t y := by
  have hb : 0 < (4 * t)⁻¹ := by positivity
  have h := norm_mul_exp_neg_le hb y
  have hs : (Real.sqrt (4 * t)⁻¹)⁻¹ = 2 * Real.sqrt t := by
    rw [Real.sqrt_inv, inv_inv, Real.sqrt_mul (by norm_num)]
    have : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [this]
  have hb2 : (4 * t)⁻¹ / 2 = (8 * t)⁻¹ := by
    field_simp
    ring
  rw [hs, hb2] at h
  have hC : 0 ≤ (4 * π * t) ^ (-(d : ℝ) / 2) := (Real.rpow_pos_of_pos (by positivity) _).le
  unfold halfGauss
  rw [heatKernel_eq]
  calc ‖y‖ * ((4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-(4 * t)⁻¹ * ‖y‖ ^ 2))
      = (4 * π * t) ^ (-(d : ℝ) / 2) * (‖y‖ * Real.exp (-(4 * t)⁻¹ * ‖y‖ ^ 2)) := by ring
    _ ≤ (4 * π * t) ^ (-(d : ℝ) / 2) * (2 * Real.sqrt t * Real.exp (-(8 * t)⁻¹ * ‖y‖ ^ 2)) := by
        gcongr
    _ = 2 * Real.sqrt t * ((4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-(8 * t)⁻¹ * ‖y‖ ^ 2)) := by
        ring

/-- The factor `‖y‖²` is absorbed by the heat kernel at the price `4t`, at half the Gaussian
strength. -/
private theorem norm_sq_mul_heatKernel_le {t : ℝ} (ht : 0 < t) (y : Euc d) :
    ‖y‖ ^ 2 * heatKernel d t y ≤ 4 * t * halfGauss d t y := by
  have hb : 0 < (4 * t)⁻¹ := by positivity
  have h := norm_sq_mul_exp_neg_le hb y
  have hb2 : (4 * t)⁻¹ / 2 = (8 * t)⁻¹ := by
    field_simp
    ring
  rw [inv_inv, hb2] at h
  have hC : 0 ≤ (4 * π * t) ^ (-(d : ℝ) / 2) := (Real.rpow_pos_of_pos (by positivity) _).le
  unfold halfGauss
  rw [heatKernel_eq]
  calc ‖y‖ ^ 2 * ((4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-(4 * t)⁻¹ * ‖y‖ ^ 2))
      = (4 * π * t) ^ (-(d : ℝ) / 2) * (‖y‖ ^ 2 * Real.exp (-(4 * t)⁻¹ * ‖y‖ ^ 2)) := by ring
    _ ≤ (4 * π * t) ^ (-(d : ℝ) / 2) * (4 * t * Real.exp (-(8 * t)⁻¹ * ‖y‖ ^ 2)) := by
        gcongr
    _ = 4 * t * ((4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-(8 * t)⁻¹ * ‖y‖ ^ 2)) := by
        ring

/-- The pointwise bound `|∂_u p_t(y)| ≤ (‖u‖ / √t) · (4πt)^{-d/2} exp(-‖y‖²/(8t))`. -/
private theorem abs_dirDeriv_heatKernel_le {t : ℝ} (ht : 0 < t) (u y : Euc d) :
    |dirDeriv u (heatKernel d t) y| ≤ ‖u‖ / Real.sqrt t * halfGauss d t y := by
  have h1 : dirDeriv u (heatKernel d t) y = -(⟪y, u⟫ / (2 * t)) * heatKernel d t y :=
    fderiv_heatKernel_apply ht y u
  rw [h1, abs_mul, abs_neg, abs_div, abs_of_pos (by positivity : 0 < 2 * t),
    abs_of_nonneg (heatKernel_nonneg ht y)]
  have hin : |⟪y, u⟫| ≤ ‖y‖ * ‖u‖ := abs_real_inner_le_norm y u
  have hk := norm_mul_heatKernel_le ht y
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hst : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hp := heatKernel_nonneg ht y
  calc |⟪y, u⟫| / (2 * t) * heatKernel d t y
      ≤ (‖y‖ * ‖u‖) / (2 * t) * heatKernel d t y := by gcongr
    _ = ‖u‖ / (2 * t) * (‖y‖ * heatKernel d t y) := by ring
    _ ≤ ‖u‖ / (2 * t) * (2 * Real.sqrt t * halfGauss d t y) := by gcongr
    _ = ‖u‖ / Real.sqrt t * halfGauss d t y := by
        have key : 2 * t = 2 * Real.sqrt t * Real.sqrt t := by rw [mul_assoc, hst]
        rw [key]
        field_simp

/-- The pointwise bound for the second derivative: `|∂_w ∂_u p_t(y)|` is at most
`‖u‖‖w‖/t · (4πt)^{-d/2} exp(-‖y‖²/(8t)) + ‖u‖‖w‖/(2t) · p_t(y)`. -/
private theorem abs_dirDeriv_dirDeriv_heatKernel_le {t : ℝ} (ht : 0 < t) (u w y : Euc d) :
    |dirDeriv w (dirDeriv u (heatKernel d t)) y| ≤
      ‖u‖ * ‖w‖ / t * halfGauss d t y + ‖u‖ * ‖w‖ / (2 * t) * heatKernel d t y := by
  have h1 : dirDeriv w (dirDeriv u (heatKernel d t)) y =
      (⟪y, w⟫ * ⟪y, u⟫ / (4 * t ^ 2) - ⟪w, u⟫ / (2 * t)) * heatKernel d t y :=
    fderiv_fderiv_heatKernel_apply ht y w u
  have hp := heatKernel_nonneg ht y
  have hin1 : |⟪y, w⟫| ≤ ‖y‖ * ‖w‖ := abs_real_inner_le_norm y w
  have hin2 : |⟪y, u⟫| ≤ ‖y‖ * ‖u‖ := abs_real_inner_le_norm y u
  have hin3 : |⟪w, u⟫| ≤ ‖w‖ * ‖u‖ := abs_real_inner_le_norm w u
  have hk := norm_sq_mul_heatKernel_le ht y
  have ht2 : 0 < 4 * t ^ 2 := by positivity
  have hA : |⟪y, w⟫ * ⟪y, u⟫ / (4 * t ^ 2)| ≤ ‖y‖ ^ 2 * (‖u‖ * ‖w‖) / (4 * t ^ 2) := by
    rw [abs_div, abs_mul, abs_of_pos ht2]
    refine div_le_div_of_nonneg_right ?_ ht2.le
    calc |⟪y, w⟫| * |⟪y, u⟫| ≤ (‖y‖ * ‖w‖) * (‖y‖ * ‖u‖) := by gcongr
      _ = ‖y‖ ^ 2 * (‖u‖ * ‖w‖) := by ring
  have hB : |⟪w, u⟫ / (2 * t)| ≤ ‖u‖ * ‖w‖ / (2 * t) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * t)]
    gcongr
    calc |⟪w, u⟫| ≤ ‖w‖ * ‖u‖ := hin3
      _ = ‖u‖ * ‖w‖ := by ring
  rw [h1, abs_mul, abs_of_nonneg hp]
  calc |⟪y, w⟫ * ⟪y, u⟫ / (4 * t ^ 2) - ⟪w, u⟫ / (2 * t)| * heatKernel d t y
      ≤ (‖y‖ ^ 2 * (‖u‖ * ‖w‖) / (4 * t ^ 2) + ‖u‖ * ‖w‖ / (2 * t)) * heatKernel d t y := by
        gcongr
        exact (abs_sub _ _).trans (add_le_add hA hB)
    _ = ‖u‖ * ‖w‖ / (4 * t ^ 2) * (‖y‖ ^ 2 * heatKernel d t y) +
          ‖u‖ * ‖w‖ / (2 * t) * heatKernel d t y := by ring
    _ ≤ ‖u‖ * ‖w‖ / (4 * t ^ 2) * (4 * t * halfGauss d t y) +
          ‖u‖ * ‖w‖ / (2 * t) * heatKernel d t y := by gcongr
    _ = ‖u‖ * ‖w‖ / t * halfGauss d t y + ‖u‖ * ‖w‖ / (2 * t) * heatKernel d t y := by
        field_simp

/-- **`L¹` integrability of the first space derivative of the heat kernel.** -/
theorem integrable_dirDeriv_heatKernel {t : ℝ} (ht : 0 < t) (u : Euc d) :
    Integrable (dirDeriv u (heatKernel d t)) := by
  have hc : Continuous (dirDeriv u (heatKernel d t)) :=
    (contDiff_dirDeriv ((contDiff_heatKernel t).of_le le_top) u).continuous
  refine Integrable.mono' ((integrable_halfGauss ht).const_mul (‖u‖ / Real.sqrt t))
    hc.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  exact abs_dirDeriv_heatKernel_le ht u y

/-- **`L¹` bound for the first space derivative of the heat kernel**:
`∫ |∂_u p_t| ≤ 2^{d/2} ‖u‖ / √t`. -/
theorem integral_abs_dirDeriv_heatKernel_le {t : ℝ} (ht : 0 < t) (u : Euc d) :
    ∫ y, |dirDeriv u (heatKernel d t) y| ≤ 2 ^ ((d : ℝ) / 2) * ‖u‖ / Real.sqrt t := by
  have hint := (integrable_dirDeriv_heatKernel ht u).abs
  have hG := (integrable_halfGauss (d := d) ht).const_mul (‖u‖ / Real.sqrt t)
  calc ∫ y, |dirDeriv u (heatKernel d t) y|
      ≤ ∫ y, ‖u‖ / Real.sqrt t * halfGauss d t y :=
        integral_mono hint hG fun y => abs_dirDeriv_heatKernel_le ht u y
    _ = ‖u‖ / Real.sqrt t * 2 ^ ((d : ℝ) / 2) := by
        rw [integral_const_mul, integral_halfGauss ht]
    _ = 2 ^ ((d : ℝ) / 2) * ‖u‖ / Real.sqrt t := by ring

/-- **`L¹` integrability of the second space derivative of the heat kernel.** -/
theorem integrable_dirDeriv_dirDeriv_heatKernel {t : ℝ} (ht : 0 < t) (u w : Euc d) :
    Integrable (dirDeriv w (dirDeriv u (heatKernel d t))) := by
  have hc : Continuous (dirDeriv w (dirDeriv u (heatKernel d t))) :=
    (contDiff_dirDeriv (contDiff_dirDeriv ((contDiff_heatKernel t).of_le le_top) u) w).continuous
  have hG := ((integrable_halfGauss (d := d) ht).const_mul (‖u‖ * ‖w‖ / t)).add
    ((integrable_heatKernel (d := d) ht).const_mul (‖u‖ * ‖w‖ / (2 * t)))
  refine Integrable.mono' hG hc.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  exact abs_dirDeriv_dirDeriv_heatKernel_le ht u w y

/-- **`L¹` bound for the second space derivative of the heat kernel**:
`∫ |∂_w ∂_u p_t| ≤ (2^{d/2} + 1) ‖u‖ ‖w‖ / t`. -/
theorem integral_abs_dirDeriv_dirDeriv_heatKernel_le {t : ℝ} (ht : 0 < t) (u w : Euc d) :
    ∫ y, |dirDeriv w (dirDeriv u (heatKernel d t)) y| ≤
      (2 ^ ((d : ℝ) / 2) + 1) * ‖u‖ * ‖w‖ / t := by
  have hint := (integrable_dirDeriv_dirDeriv_heatKernel ht u w).abs
  have hG1 := (integrable_halfGauss (d := d) ht).const_mul (‖u‖ * ‖w‖ / t)
  have hG2 := (integrable_heatKernel (d := d) ht).const_mul (‖u‖ * ‖w‖ / (2 * t))
  have hnn : 0 ≤ ‖u‖ * ‖w‖ / t := by positivity
  calc ∫ y, |dirDeriv w (dirDeriv u (heatKernel d t)) y|
      ≤ ∫ y, (‖u‖ * ‖w‖ / t * halfGauss d t y + ‖u‖ * ‖w‖ / (2 * t) * heatKernel d t y) :=
        integral_mono hint (hG1.add hG2) fun y => abs_dirDeriv_dirDeriv_heatKernel_le ht u w y
    _ = ‖u‖ * ‖w‖ / t * 2 ^ ((d : ℝ) / 2) + ‖u‖ * ‖w‖ / (2 * t) * 1 := by
        rw [integral_add hG1 hG2, integral_const_mul, integral_const_mul, integral_halfGauss ht,
          integral_heatKernel ht]
    _ ≤ ‖u‖ * ‖w‖ / t * 2 ^ ((d : ℝ) / 2) + ‖u‖ * ‖w‖ / t * 1 := by
        gcongr
        linarith
    _ = (2 ^ ((d : ℝ) / 2) + 1) * ‖u‖ * ‖w‖ / t := by ring

end

end LatticeProb.Analysis.Schauder
