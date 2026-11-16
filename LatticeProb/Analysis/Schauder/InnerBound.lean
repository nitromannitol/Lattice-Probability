import LatticeProb.Analysis.Schauder.Continuum

/-!
# The inner part of a Hölder convolution estimate

Let `χ` be a bump function supported in the ball of radius `rOut` around the origin, `K` a
continuous kernel and `g` a continuous function. If `g` is Hölder continuous at `x` on that ball,
`|g (x - y) - g x| ≤ K₁ ‖y‖ ^ α` for `‖y‖ < rOut`, and the kernel is such that `|K y| ‖y‖ ^ α` is
dominated by an integrable function `H`, then

`|∫ χ y * K y * (g (x - y) - g x) dy| ≤ K₁ * ∫ H`.

Near the origin the kernel only sees the Hölder modulus of `g` at `x`. The proof is a pointwise
bound of the integrand by `K₁ * H y`: inside the support `χ` is at most `1` and the Hölder bound
applies, outside it `χ` vanishes.
-/

namespace LatticeProb.Analysis.Schauder

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Pointwise, the localized integrand is bounded by `K₁ * H y`: inside the ball of radius
`rOut` the cutoff is at most `1` and the Hölder bound of `g` at `x` applies, outside the ball the
cutoff vanishes. -/
theorem norm_bump_mul_sub_le (χ : ContDiffBump (0 : Euc d)) {K g H : Euc d → ℝ}
    {x : Euc d} {K₁ α : ℝ} (hKH : ∀ y, |K y| * ‖y‖ ^ α ≤ H y) (hK₁ : 0 ≤ K₁)
    (hgx : ∀ y, ‖y‖ < χ.rOut → |g (x - y) - g x| ≤ K₁ * ‖y‖ ^ α) (y : Euc d) :
    ‖χ y * K y * (g (x - y) - g x)‖ ≤ K₁ * H y := by
  have hpow : 0 ≤ ‖y‖ ^ α := Real.rpow_nonneg (norm_nonneg y) α
  have hH : 0 ≤ H y := le_trans (mul_nonneg (abs_nonneg _) hpow) (hKH y)
  by_cases hy : ‖y‖ < χ.rOut
  · have hχ0 : 0 ≤ χ y := χ.nonneg
    have hχ1 : χ y ≤ 1 := χ.le_one
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hχ0]
    calc χ y * |K y| * |g (x - y) - g x| ≤ 1 * |K y| * (K₁ * ‖y‖ ^ α) := by
          gcongr
          exact hgx y hy
      _ = K₁ * (|K y| * ‖y‖ ^ α) := by ring
      _ ≤ K₁ * H y := mul_le_mul_of_nonneg_left (hKH y) hK₁
  · have hdist : χ.rOut ≤ dist y 0 := by
      rw [dist_zero_right]
      exact not_lt.mp hy
    rw [χ.zero_of_le_dist hdist]
    simpa using mul_nonneg hK₁ hH

/-- Near the origin the kernel only sees the Hölder modulus of `g` at `x`: if `g` is Hölder
continuous at `x` on the ball of radius `rOut` of the bump `χ`, and `|K y| ‖y‖ ^ α` is dominated
by an integrable function `H`, then the localized convolution of `K` with the increment of `g`
at `x` is bounded by `K₁ * ∫ H`. -/
theorem abs_integral_bump_mul_sub_le (χ : ContDiffBump (0 : Euc d)) {K g H : Euc d → ℝ}
    {x : Euc d} {K₁ α : ℝ} (hK : Continuous K) (hg : Continuous g) (hH : Integrable H)
    (hKH : ∀ y, |K y| * ‖y‖ ^ α ≤ H y) (hK₁ : 0 ≤ K₁)
    (hgx : ∀ y, ‖y‖ < χ.rOut → |g (x - y) - g x| ≤ K₁ * ‖y‖ ^ α) :
    |∫ y, χ y * K y * (g (x - y) - g x)| ≤ K₁ * ∫ y, H y := by
  have hcont : Continuous fun y : Euc d => χ y * K y * (g (x - y) - g x) :=
    (χ.continuous.mul hK).mul
      ((hg.comp (continuous_const.sub continuous_id)).sub continuous_const)
  have hbound := norm_bump_mul_sub_le χ hKH hK₁ hgx
  have hint : Integrable fun y : Euc d => χ y * K y * (g (x - y) - g x) :=
    (hH.const_mul K₁).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  calc |∫ y, χ y * K y * (g (x - y) - g x)| ≤ ∫ y, |χ y * K y * (g (x - y) - g x)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y, K₁ * H y := integral_mono hint.abs (hH.const_mul K₁) hbound
    _ = K₁ * ∫ y, H y := integral_const_mul K₁ H

end

end LatticeProb.Analysis.Schauder
