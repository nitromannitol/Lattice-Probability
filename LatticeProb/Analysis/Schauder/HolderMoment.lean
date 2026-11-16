import LatticeProb.Analysis.Schauder.KernelDerivSpace
import LatticeProb.Analysis.Schauder.SineCoeff

/-!
# Hölder moment of the second derivative of the heat kernel

For `p_t(x) = (4πt)^{-d/2} exp(-‖x‖²/(4t))` on `ℝ^d`, `t > 0` and `0 ≤ α ≤ 1`, the second
directional derivatives of `p_t` along unit directions satisfy the pointwise bound
`|∂_a ∂_b p_t(y)| ‖y‖^α ≤ 32 · 2^{d/2} · t^{α/2 - 1} · p_{2t}(y)`.

The proof writes `r = ‖y‖²/t`. The explicit formula of `KernelDerivSpace.lean` bounds the second
derivative by `(r/4 + 1/2) p_t(y) / t`; the moment satisfies `‖y‖^α ≤ t^{α/2} (1 + r)`; and the
kernel splits as `p_t(y) = 2^{d/2} exp(-r/8) p_{2t}(y)`. What remains is the scalar inequality
`(r/4 + 1/2)(1 + r) exp(-r/8) ≤ 32`, which follows from `1 + q + q²/2 ≤ exp q` at `q = r/8`.
-/

namespace LatticeProb.Analysis.Schauder

open Real

open scoped RealInnerProductSpace

noncomputable section

variable {d : ℕ}

/-- The Hölder moment is dominated by a quadratic moment at the matching scale:
`s^α ≤ t^{α/2} (1 + s²/t)` for `s ≥ 0`, `t > 0` and `0 ≤ α ≤ 1`. -/
private theorem rpow_le_rpow_half_mul_one_add {t α : ℝ} (ht : 0 < t) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) {s : ℝ} (hs : 0 ≤ s) : s ^ α ≤ t ^ (α / 2) * (1 + s ^ 2 / t) := by
  have hq : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hu0 : 0 ≤ s / Real.sqrt t := by positivity
  have h1 : (s / Real.sqrt t) ^ α ≤ 1 + (s / Real.sqrt t) ^ 2 := by
    rcases le_total (s / Real.sqrt t) 1 with h | h
    · have := Real.rpow_le_one hu0 h hα0
      nlinarith [sq_nonneg (s / Real.sqrt t)]
    · calc (s / Real.sqrt t) ^ α ≤ (s / Real.sqrt t) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h hα1
        _ = s / Real.sqrt t := Real.rpow_one _
        _ ≤ 1 + (s / Real.sqrt t) ^ 2 := by nlinarith [sq_nonneg (s / Real.sqrt t - 1)]
  have h2 : s ^ α = t ^ (α / 2) * (s / Real.sqrt t) ^ α := by
    have hs' : s = Real.sqrt t * (s / Real.sqrt t) := by field_simp
    have hroot : Real.sqrt t ^ α = t ^ (α / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
      congr 1
      ring
    calc s ^ α = (Real.sqrt t * (s / Real.sqrt t)) ^ α := by rw [← hs']
      _ = Real.sqrt t ^ α * (s / Real.sqrt t) ^ α := Real.mul_rpow hq.le hu0
      _ = t ^ (α / 2) * (s / Real.sqrt t) ^ α := by rw [hroot]
  have h3 : (s / Real.sqrt t) ^ 2 = s ^ 2 / t := by
    rw [div_pow, Real.sq_sqrt ht.le]
  rw [h2, ← h3]
  exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg ht.le _)

/-- The scalar inequality `(r/4 + 1/2)(1 + r) exp(-r/8) ≤ 32` for `r ≥ 0`. -/
private theorem scalar_bound {r : ℝ} (hr : 0 ≤ r) :
    (r / 4 + 1 / 2) * (1 + r) * Real.exp (-(r / 8)) ≤ 32 := by
  have hq : 0 ≤ r / 8 := by positivity
  have h := Real.quadratic_le_exp_of_nonneg hq
  have hmul : Real.exp (-(r / 8)) * Real.exp (r / 8) = 1 := by
    rw [← Real.exp_add]
    simp
  have hpoly : (r / 4 + 1 / 2) * (1 + r) ≤ 32 * Real.exp (r / 8) := by
    nlinarith [sq_nonneg r]
  calc (r / 4 + 1 / 2) * (1 + r) * Real.exp (-(r / 8))
      ≤ 32 * Real.exp (r / 8) * Real.exp (-(r / 8)) := by gcongr
    _ = 32 := by rw [mul_assoc, mul_comm (Real.exp (r / 8)), hmul, mul_one]

/-- **Hölder moment of the second derivative of the heat kernel.** For `t > 0`, `0 ≤ α ≤ 1` and
unit-bounded directions `a`, `b`,
`|∂_a ∂_b p_t(y)| ‖y‖^α ≤ 32 · 2^{d/2} · t^{α/2 - 1} · p_{2t}(y)`. -/
theorem abs_dirDeriv_dirDeriv_heatKernel_mul_rpow_le {t α : ℝ} (ht : 0 < t) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) {a b : Euc d} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (y : Euc d) :
    |dirDeriv a (dirDeriv b (heatKernel d t)) y| * ‖y‖ ^ α ≤
      32 * 2 ^ ((d : ℝ) / 2) * t ^ (α / 2 - 1) * heatKernel d (2 * t) y := by
  have h1 : dirDeriv a (dirDeriv b (heatKernel d t)) y =
      (⟪y, a⟫ * ⟪y, b⟫ / (4 * t ^ 2) - ⟪a, b⟫ / (2 * t)) * heatKernel d t y :=
    fderiv_fderiv_heatKernel_apply ht y a b
  have hp := heatKernel_nonneg ht y
  have ht2 : 0 < 4 * t ^ 2 := by positivity
  have hyn : 0 ≤ ‖y‖ := norm_nonneg y
  have hin1 : |⟪y, a⟫| ≤ ‖y‖ := by
    calc |⟪y, a⟫| ≤ ‖y‖ * ‖a‖ := abs_real_inner_le_norm y a
      _ ≤ ‖y‖ * 1 := by gcongr
      _ = ‖y‖ := mul_one _
  have hin2 : |⟪y, b⟫| ≤ ‖y‖ := by
    calc |⟪y, b⟫| ≤ ‖y‖ * ‖b‖ := abs_real_inner_le_norm y b
      _ ≤ ‖y‖ * 1 := by gcongr
      _ = ‖y‖ := mul_one _
  have hin3 : |⟪a, b⟫| ≤ 1 := by
    calc |⟪a, b⟫| ≤ ‖a‖ * ‖b‖ := abs_real_inner_le_norm a b
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := mul_one _
  have hA : |⟪y, a⟫ * ⟪y, b⟫ / (4 * t ^ 2)| ≤ ‖y‖ ^ 2 / (4 * t ^ 2) := by
    rw [abs_div, abs_mul, abs_of_pos ht2]
    refine div_le_div_of_nonneg_right ?_ ht2.le
    calc |⟪y, a⟫| * |⟪y, b⟫| ≤ ‖y‖ * ‖y‖ := by gcongr
      _ = ‖y‖ ^ 2 := by ring
  have hB : |⟪a, b⟫ / (2 * t)| ≤ 1 / (2 * t) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * t)]
    gcongr
  have hD : |dirDeriv a (dirDeriv b (heatKernel d t)) y| ≤
      (‖y‖ ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) * heatKernel d t y := by
    rw [h1, abs_mul, abs_of_nonneg hp]
    gcongr
    exact (abs_sub _ _).trans (add_le_add hA hB)
  have hM := rpow_le_rpow_half_mul_one_add ht hα0 hα1 hyn
  have hr : 0 ≤ ‖y‖ ^ 2 / t := by positivity
  have hsc := scalar_bound hr
  have hsplit := heatKernel_eq_two_pow_mul_exp_mul_heatKernel_two_mul ht y
  have hQ := heatKernel_nonneg (by positivity : 0 < 2 * t) y
  have hpow : t ^ (α / 2 - 1) = t ^ (α / 2) / t := Real.rpow_sub_one ht.ne' _
  have hpow0 : 0 ≤ t ^ (α / 2) := Real.rpow_nonneg ht.le _
  have hK : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  calc |dirDeriv a (dirDeriv b (heatKernel d t)) y| * ‖y‖ ^ α
      ≤ ((‖y‖ ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) * heatKernel d t y) *
          (t ^ (α / 2) * (1 + ‖y‖ ^ 2 / t)) := by gcongr
    _ = t ^ (α / 2) / t * (((‖y‖ ^ 2 / t) / 4 + 1 / 2) * (1 + ‖y‖ ^ 2 / t)) *
          heatKernel d t y := by
        field_simp
    _ = t ^ (α / 2) / t * (((‖y‖ ^ 2 / t) / 4 + 1 / 2) * (1 + ‖y‖ ^ 2 / t) *
          Real.exp (-(‖y‖ ^ 2 / t / 8))) * (2 ^ ((d : ℝ) / 2) * heatKernel d (2 * t) y) := by
        rw [hsplit]
        ring
    _ ≤ t ^ (α / 2) / t * 32 * (2 ^ ((d : ℝ) / 2) * heatKernel d (2 * t) y) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsc (by positivity)) (by positivity)
    _ = 32 * 2 ^ ((d : ℝ) / 2) * t ^ (α / 2 - 1) * heatKernel d (2 * t) y := by
        rw [hpow]
        ring

end

end LatticeProb.Analysis.Schauder
