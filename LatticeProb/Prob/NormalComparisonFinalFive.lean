/-
# Li--Shao normal comparison: the `2 × 2` Gaussian density as the bivariate density

Route item 5, the algebraic core.  The boundary integral of the density along the smart path
(`LatticeProb/Prob/GaussCovDensityBoundary.lean` in the route) is dominated by the `2 × 2`
Gaussian density of the pair `!![v, c; c, v]`, and that `2 × 2` density is the bivariate Gaussian
density `bivariateGaussDensity v (c / v) a b` at variance `v` and correlation `c / v`.  This file
proves the determinant, positive definiteness, inverse, quadratic form and density of
`!![v, c; c, v]` for `|c| < v`.

  `covDensity !![v, c; c, v] ![a, b] = bivariateGaussDensity v (c / v) a b`.

No `External` is touched, no `Prop` is frozen, and nothing is claimed about `Rotor.External.LSS`.
-/
import LatticeProb.Prob.NormalComparisonBoundary
import LatticeProb.Prob.NormalComparisonCovariance

open MeasureTheory Matrix

namespace LatticeProb

/-- The determinant of the `2 × 2` covariance matrix with common variance `v` and covariance
`c`. -/
theorem det_two_cov {v c : ℝ} :
    (!![v, c; c, v] : Matrix (Fin 2) (Fin 2) ℝ).det = v ^ 2 - c ^ 2 := by
  rw [Matrix.det_fin_two_of]
  ring

/-- The `2 × 2` covariance matrix with common variance `v` and covariance `c`, `|c| < v`, is
positive definite. -/
theorem posDef_two_cov {v c : ℝ} (_hv : 0 < v) (hc : |c| < v) :
    (!![v, c; c, v] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  have hc' := abs_lt.mp hc
  have hvc1 : 0 < v + c := by linarith [hc'.1]
  have hvc2 : 0 < v - c := by linarith [hc'.2]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp
  · intro x hx
    have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (funext fun i => by fin_cases i <;> simp [h.1, h.2])
    have hform : star x ⬝ᵥ ((!![v, c; c, v] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x)
        = (v + c) / 2 * (x 0 + x 1) ^ 2 + (v - c) / 2 * (x 0 - x 1) ^ 2 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hform]
    have hpq : 0 < (x 0 + x 1) ^ 2 ∨ 0 < (x 0 - x 1) ^ 2 := by
      by_contra h
      push Not at h
      have h1 : x 0 + x 1 = 0 := by nlinarith [sq_nonneg (x 0 + x 1)]
      have h2 : x 0 - x 1 = 0 := by nlinarith [sq_nonneg (x 0 - x 1)]
      rcases hx' with h0 | h0 <;> [exact h0 (by linarith); exact h0 (by linarith)]
    rcases hpq with h | h
    · have := mul_pos (div_pos hvc1 two_pos) h
      nlinarith [mul_nonneg (div_pos hvc2 two_pos).le (sq_nonneg (x 0 - x 1))]
    · have := mul_pos (div_pos hvc2 two_pos) h
      nlinarith [mul_nonneg (div_pos hvc1 two_pos).le (sq_nonneg (x 0 + x 1))]

/-- The inverse of the `2 × 2` covariance matrix with common variance `v` and covariance `c`:
`(v² - c²)⁻¹ • !![v, -c; -c, v]`. -/
theorem inv_two_cov {v c : ℝ} (_hv : 0 < v) (hc : |c| < v) :
    (!![v, c; c, v] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
      = (v ^ 2 - c ^ 2)⁻¹ • !![v, -c; -c, v] := by
  have hc' := abs_lt.mp hc
  have hd : v ^ 2 - c ^ 2 ≠ 0 := by nlinarith [hc'.1, hc'.2]
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- The quadratic form of the inverse of the `2 × 2` covariance matrix:
`![a, b] ⬝ᵥ (M⁻¹ *ᵥ ![a, b]) = (v a² - 2 c a b + v b²) / (v² - c²)`. -/
theorem quadForm_two_cov {v c : ℝ} (hv : 0 < v) (hc : |c| < v) (a b : ℝ) :
    (![a, b] : Fin 2 → ℝ)
        ⬝ᵥ ((!![v, c; c, v] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *ᵥ ![a, b])
      = (v * a ^ 2 - 2 * c * a * b + v * b ^ 2) / (v ^ 2 - c ^ 2) := by
  rw [inv_two_cov hv hc]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- **The density of `N(0, !![v, c; c, v])` is the bivariate Gaussian density** at variance `v`
and correlation `c / v`. -/
theorem covDensity_two_cov {v c : ℝ} (hv : 0 < v) (hc : |c| < v) (a b : ℝ) :
    covDensity (!![v, c; c, v] : Matrix (Fin 2) (Fin 2) ℝ) ![a, b]
      = bivariateGaussDensity v (c / v) a b := by
  have hc' := abs_lt.mp hc
  have hd : 0 < v ^ 2 - c ^ 2 := by nlinarith [hv, hc'.1, hc'.2]
  have hr : 1 - (c / v) ^ 2 = (v ^ 2 - c ^ 2) / v ^ 2 := by
    field_simp
  have hr0 : 0 < 1 - (c / v) ^ 2 := by rw [hr]; positivity
  have h2pi : (2 * Real.pi) ^ (-((2 : ℕ) : ℝ) / 2) = (2 * Real.pi)⁻¹ := by
    have h : -((2 : ℕ) : ℝ) / 2 = -1 := by norm_num
    rw [h, Real.rpow_neg_one]
  have hdet : (v ^ 2 - c ^ 2) ^ (-(1 : ℝ) / 2) = (v * Real.sqrt (1 - (c / v) ^ 2))⁻¹ := by
    have hsq : v ^ 2 - c ^ 2 = (v * v) * (1 - (c / v) ^ 2) := by
      rw [hr]; field_simp
    rw [Real.rpow_div_two_eq_sqrt _ hd.le, Real.rpow_neg_one, hsq,
      Real.sqrt_mul (mul_self_nonneg v), Real.sqrt_mul_self hv.le]
  have hexp : -((![a, b] : Fin 2 → ℝ) ⬝ᵥ
        ((!![v, c; c, v] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *ᵥ ![a, b])) / 2
      = -(a ^ 2 - 2 * (c / v) * a * b + b ^ 2) / (2 * v * (1 - (c / v) ^ 2)) := by
    rw [quadForm_two_cov hv hc, hr]
    have hv0 : v ≠ 0 := hv.ne'
    have hd0 : v ^ 2 - c ^ 2 ≠ 0 := hd.ne'
    field_simp
  unfold covDensity bivariateGaussDensity
  rw [det_two_cov, h2pi, hdet, hexp, mul_inv, mul_inv, mul_inv]
  ring

end LatticeProb
