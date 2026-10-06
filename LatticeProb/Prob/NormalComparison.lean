/-
# Normal comparison (Li--Shao) for the multivariate Gaussian: elementary steps

Route: `scratch/pk/normalcompare-route.md`, continuing on top of
`LatticeProb/Gauss/MultivariateDensity.lean`.  The frozen target is
`Sandpile.External.NormalComparison` (Li--Shao Corollary 2.1): for a centred
Gaussian on `ℝ^m` with covariance `S`, common variance `v`, and nonnegative
correlations `ρ_{ij} = S i j / v`,

  `|P(Y ≤ b) - ∏_i P(Y_i ≤ b_i)| ≤ C ∑_{i<j} ρ_{ij} exp(-(b_i² + b_j²)/(2 v (1 + ρ_{ij})))`.

This file lands the elementary half of the smart-path proof: the path from the
product law `v • 1` to `S` and the bivariate density comparison (the AM--GM bound
that produces the exponential factor).

## What is *not* landed (the named missing inputs of the route)

* `multivariateGaussian_eq_withDensity` (route item 1): the density of `N(0, S)`
  for a general positive definite `S`.  Mathlib has `multivariateGaussian` only
  as the pushforward `(stdGaussian).map (√S ·)`; the change-of-variables
  computation of the density is the remaining analytic input.
* `hasDerivAt_orthant_multivariateGaussian` (item 3): differentiating the orthant
  probability in the covariance.
* `orthant_deriv_eq_boundaryIntegral` / `boundaryIntegral_le_bivariateDensity`
  (items 4--5): the double integration by parts and the conditional factorisation.
* `∫_0^1 (1 - (t r)²)^{-1/2} dt = arcsin(r)/r ≤ π/2` (item 7), whose constant
  `π/2` gives the route's `C = max 1 (π/2) / (2π)`.  The antiderivative is
  `arcsin`, but the endpoint `r = 1` makes the integrand improper, so the
  elementary proof needs either an `intervalIntegral` substitution lemma with a
  `ContinuousOn` (not global `Continuous`) kernel, or the convexity bound
  `arcsin r ≤ (π/2) r`.

With items 1, 3, 4, 5 and 7, the interpolation `∫_0^1 deriv F t dt` plus the two
real inequalities proved here closes the Li--Shao bound.
-/
import LatticeProb.Gauss.MultivariateDensity
import LatticeProb.Prob.GaussDensity

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal MatrixOrder

namespace LatticeProb

/-! ### The smart path -/

/-- The smart path of the Li--Shao route: `S_t = (1 - t) • (v • 1) + t • S`, joining
the product law `v • 1` at `t = 0` to `S` at `t = 1`. -/
noncomputable def normalComparisonSmartPath {m : ℕ} (v : ℝ) (S : Matrix (Fin m) (Fin m) ℝ)
    (t : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (1 - t) • (v • 1) + t • S

/-- The smart path starts at the product law. -/
theorem normalComparisonSmartPath_zero {m : ℕ} (v : ℝ) (S : Matrix (Fin m) (Fin m) ℝ) :
    normalComparisonSmartPath v S 0 = v • 1 := by
  simp [normalComparisonSmartPath]

/-- The smart path ends at `S`. -/
theorem normalComparisonSmartPath_one {m : ℕ} (v : ℝ) (S : Matrix (Fin m) (Fin m) ℝ) :
    normalComparisonSmartPath v S 1 = S := by
  simp [normalComparisonSmartPath]

/-- The smart path keeps the diagonal `v`, so the common variance is constant along it. -/
theorem normalComparisonSmartPath_diag {m : ℕ} {v : ℝ} {S : Matrix (Fin m) (Fin m) ℝ}
    (hdiag : ∀ i, S i i = v) (t : ℝ) (i : Fin m) :
    normalComparisonSmartPath v S t i i = v := by
  have hone : (v • (1 : Matrix (Fin m) (Fin m) ℝ)) i i = v := by simp
  simp only [normalComparisonSmartPath, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    hone, hdiag i]
  ring

/-- The smart path keeps every entry nonnegative for `t ∈ [0,1]`, since both endpoints do. -/
theorem normalComparisonSmartPath_nonneg {m : ℕ} {v : ℝ} {S : Matrix (Fin m) (Fin m) ℝ}
    (hoff : ∀ i j, 0 ≤ S i j) (hv : 0 ≤ v) {t : ℝ} (ht : t ∈ Set.Icc 0 1) (i j : Fin m) :
    0 ≤ normalComparisonSmartPath v S t i j := by
  have h1 : 0 ≤ 1 - t := by linarith [ht.2]
  have h2 : 0 ≤ t := ht.1
  have hv1 : 0 ≤ (v • (1 : Matrix (Fin m) (Fin m) ℝ)) i j := by
    by_cases h : i = j
    · subst h; simp [hv]
    · simp [h]
  simpa only [normalComparisonSmartPath, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using
    add_nonneg (mul_nonneg h1 hv1) (mul_nonneg h2 (hoff i j))

/-! ### The bivariate Gaussian density at correlation `r` -/

/-- The bivariate Gaussian density at variance `v` and correlation `r`:
`1 / (2 π v √(1 - r²)) * exp (-(a² - 2 r a b + b²) / (2 v (1 - r²)))`. -/
noncomputable def bivariateGaussDensity (v r a b : ℝ) : ℝ :=
  (2 * Real.pi * v * Real.sqrt (1 - r ^ 2))⁻¹ *
    Real.exp (-(a ^ 2 - 2 * r * a * b + b ^ 2) / (2 * v * (1 - r ^ 2)))

/-- **The exponent comparison.**  For `0 ≤ r < 1`, `0 ≤ t ≤ 1` with `t r < 1`, the bivariate
exponent with correlation `t r` is at most the frozen expression's exponent with correlation `r`.

The proof is `2 a b ≤ a² + b²` together with `(t r - 1) (t r - r) ≥ 0`, the latter
being the route's `t (1 + r) ≤ 1 + t² r` for `0 ≤ r` and `0 ≤ t ≤ 1`. -/
theorem bivariateExpArg_le {v r t a b : ℝ} (hv : 0 < v) (hr0 : 0 ≤ r)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htr : t * r < 1) :
    -(a ^ 2 - 2 * (t * r) * a * b + b ^ 2) / (2 * v * (1 - (t * r) ^ 2))
      ≤ -(a ^ 2 + b ^ 2) / (2 * v * (1 + r)) := by
  have htr0 : 0 ≤ t * r := mul_nonneg ht0 hr0
  have hsq : (t * r) ^ 2 < 1 := by
    have h : (t * r) * (t * r) ≤ t * r := mul_le_of_le_one_right htr0 htr.le
    nlinarith
  have hden : 0 < 2 * v * (1 - (t * r) ^ 2) := by nlinarith
  have hden' : 0 < 2 * v * (1 + r) := by nlinarith
  rw [div_le_div_iff₀ hden hden']
  have h1 : 2 * a * b ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have h2 : 2 * (t * r) * a * b * (1 + r) ≤ (t * r) * (1 + r) * (a ^ 2 + b ^ 2) := by
    have h := mul_le_mul_of_nonneg_left h1 (mul_nonneg htr0 (by linarith : (0 : ℝ) ≤ 1 + r))
    linarith [h]
  have h3 : 0 ≤ (t * r - 1) * (t * r - r) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by nlinarith [ht1, hr0])
  have h4 : (t * r) * (1 + r) * (a ^ 2 + b ^ 2) ≤ ((t * r) ^ 2 + r) * (a ^ 2 + b ^ 2) := by
    have h5 : (t * r) * (1 + r) ≤ (t * r) ^ 2 + r := by nlinarith [h3]
    exact mul_le_mul_of_nonneg_right h5 (by positivity)
  nlinarith [h2, h4]

/-- **The bivariate density bound (route item 6).**  The bivariate Gaussian density is at most
`1 / (2 π v √(1 - r²))` times the frozen single-exponential factor. -/
theorem bivariateGaussDensity_le {v r a b : ℝ} (hv : 0 < v) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    bivariateGaussDensity v r a b ≤
      (2 * Real.pi * v)⁻¹ * (Real.sqrt (1 - r ^ 2))⁻¹ *
        Real.exp (-(a ^ 2 + b ^ 2) / (2 * v * (1 + r))) := by
  have hr2 : 0 < 1 - r ^ 2 := by nlinarith
  have harg : -(a ^ 2 - 2 * r * a * b + b ^ 2) / (2 * v * (1 - r ^ 2))
      ≤ -(a ^ 2 + b ^ 2) / (2 * v * (1 + r)) := by
    have h := bivariateExpArg_le (v := v) (r := r) (t := 1) (a := a) (b := b) hv hr0
      (by norm_num) le_rfl (by linarith)
    simpa using h
  have hpre : (2 * Real.pi * v * Real.sqrt (1 - r ^ 2))⁻¹
      = (2 * Real.pi * v)⁻¹ * (Real.sqrt (1 - r ^ 2))⁻¹ := by rw [mul_inv, mul_comm]
  have hnn : 0 ≤ (2 * Real.pi * v)⁻¹ * (Real.sqrt (1 - r ^ 2))⁻¹ :=
    mul_nonneg (inv_nonneg.mpr (by positivity)) (inv_nonneg.mpr (Real.sqrt_pos.mpr hr2).le)
  rw [bivariateGaussDensity, hpre]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) hnn

/-! ### The scale integral (route item 7), recorded

The last elementary input is the closed form of the scale integral

  `∫_0^1 (1 - (t r)²)^{-1/2} dt = arcsin(r)/r ≤ π/2`   (`0 ≤ r ≤ 1`, value `1` at `r = 0`),

whose constant `π/2` is the route's `C = max 1 (π/2) / (2π)`.  It is not
formalized here: the antiderivative is `arcsin`, but the endpoint `r = 1` makes
the integrand improper, so the elementary proof needs either an
`intervalIntegral` change-of-variables lemma with a `ContinuousOn` (not global
`Continuous`) substitution kernel, or the convexity bound `arcsin r ≤ (π/2) r`
(`Real.arcsin_le_pi_div_two` alone is only the `r = 1` case). -/

end LatticeProb
