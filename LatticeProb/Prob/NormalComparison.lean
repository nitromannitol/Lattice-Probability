/-
# Normal comparison (Li--Shao) for the multivariate Gaussian: elementary steps

Route: `scratch/pk/normalcompare-route.md`, continuing on top of
`LatticeProb/Gauss/MultivariateDensity.lean`.  The frozen target is
`Sandpile.External.NormalComparison` (Li--Shao Corollary 2.1): for a centred
Gaussian on `ℝ^m` with covariance `S`, common variance `v`, and nonnegative
correlations `ρ_{ij} = S i j / v`,

  `|P(Y ≤ b) - ∏_i P(Y_i ≤ b_i)| ≤
    C ∑_{i<j} ρ_{ij} exp(-(b_i² + b_j²)/(2 v (1 + ρ_{ij})))`.

This file lands the elementary half of the smart-path proof: the path from the
product law `v • 1` to `S`, the bivariate density comparison (the AM--GM bound
that produces the exponential factor), and the closed form of the scale integral
`∫_0^1 (1 - (t r)²)^{-1/2} dt = arcsin(r)/r ≤ π/2` (route item 7).  The pieces are
adapted from the route's working scratch
(`~/lean/Divisible-Sandpile-Percolation/scratch/normalcompare_step.lean`) into
the library namespace.

## What is *not* landed (the named missing inputs of the route)

* `multivariateGaussian_eq_withDensity` (route item 1): the density of `N(0, S)`
  for a general positive definite `S`.  Mathlib has `multivariateGaussian` only
  as the pushforward `(stdGaussian).map (√S ·)`; the change-of-variables
  computation of the density is the remaining analytic input.
* `hasDerivAt_orthant_multivariateGaussian` (item 3): differentiating the orthant
  probability in the covariance.
* `orthant_deriv_eq_boundaryIntegral` / `boundaryIntegral_le_bivariateDensity`
  (items 4--5): the double integration by parts and the conditional factorisation.

With items 1, 3, 4 and 5, the interpolation `∫_0^1 deriv F t dt`, the two real
inequalities proved here, and the scale integral `≤ π/2` also proved here, closes
the Li--Shao bound.
-/
import LatticeProb.Gauss.MultivariateDensity
import LatticeProb.Prob.GaussDensity

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal MatrixOrder Matrix

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

/-! ### The scale integral (route item 7)

The antiderivative of `1/√(1-x²)` is `arcsin`, so the substitution `u = t r`
gives `∫_0^1 1/√(1-(t r)²) dt = arcsin(r)/r`, and `arcsin(r) ≤ (π/2) r` on
`[0,1]` gives the bound `≤ π/2`.  The rpow form `(1-(t r)²)^{-1/2}` is the same
integrand by `Real.sqrt_eq_rpow` and `Real.rpow_neg`, and is stated as the
corollary `integral_one_sub_sq_rpow_neg_half_le`. -/

/-- `1/√(1-x²) = x^{-1/2}` for `x > 0`. -/
private theorem rpow_neg_half_eq_one_div_sqrt {x : ℝ} (hx : 0 < x) :
    x ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt x := by
  rw [Real.sqrt_eq_rpow]
  rw [show (1 : ℝ) / x ^ (1 / 2 : ℝ) = (x ^ (1 / 2 : ℝ))⁻¹ by rw [one_div]]
  exact Real.rpow_neg hx.le (1 / 2)

/-- `arcsin r ≤ (π/2) r` for `0 ≤ r ≤ 1` (the convexity bound used to close item 7). -/
private theorem arcsin_le_pi_div_two_mul {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.arcsin r ≤ Real.pi / 2 * r := by
  rw [Real.arcsin_le_iff_le_sin ⟨by linarith, hr1⟩
    ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos, hr1]⟩]
  exact Real.le_sin_mul hr0 hr1

/-- The antiderivative `arcsin` integrates `1/√(1-x²)`:
`∫_0^r 1/√(1-u²) du = arcsin r` for `0 ≤ r < 1`. -/
theorem integral_one_div_sqrt_one_sub_sq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ u in (0 : ℝ)..r, 1 / Real.sqrt (1 - u ^ 2) = Real.arcsin r := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) r,
      HasDerivAt Real.arcsin (1 / Real.sqrt (1 - u ^ 2)) u := by
    intro u hu
    rw [Set.uIcc_of_le hr0] at hu
    exact Real.hasDerivAt_arcsin (by nlinarith [hu.1]) (by nlinarith [hu.2, hr1])
  have hint : IntervalIntegrable (fun u : ℝ => 1 / Real.sqrt (1 - u ^ 2)) volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · exact Real.continuous_sqrt.comp_continuousOn (by fun_prop)
    · intro u hu
      rw [Set.uIcc_of_le hr0] at hu
      exact ne_of_gt (Real.sqrt_pos.mpr (by nlinarith [hu.1, hu.2, hr1]))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, Real.arcsin_zero, sub_zero]

/-- **The scale integral (route item 7), exact form.**  For `0 < r < 1`,
`∫_0^1 1/√(1 - (t r)²) dt = arcsin r / r`. -/
theorem integral_one_div_sqrt_one_sub_sq_mul {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∫ t in (0 : ℝ)..1, 1 / Real.sqrt (1 - (t * r) ^ 2) = Real.arcsin r / r := by
  have hgcont : ContinuousOn (fun u : ℝ => 1 / Real.sqrt (1 - u ^ 2))
      ((fun x : ℝ => x * r) '' Set.uIcc (0 : ℝ) 1) := by
    apply ContinuousOn.div continuousOn_const
    · exact Real.continuous_sqrt.comp_continuousOn (by fun_prop)
    · intro v hv
      rcases hv with ⟨x, hx, rfl⟩
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      exact ne_of_gt (Real.sqrt_pos.mpr (by
        nlinarith [mul_nonneg hx.1 hr0.le, mul_le_of_le_one_left hr0.le hx.2,
          sq_nonneg (x * r), hr0, hr1]))
  have h := intervalIntegral.integral_comp_mul_deriv'
    (f := fun x : ℝ => x * r) (f' := fun _ => r)
    (g := fun u : ℝ => 1 / Real.sqrt (1 - u ^ 2))
    (a := (0 : ℝ)) (b := 1)
    (fun x _ => by simpa using (hasDerivAt_id x).mul_const r)
    (by fun_prop) hgcont
  simp only [Function.comp_apply, zero_mul, one_mul] at h
  rw [integral_one_div_sqrt_one_sub_sq hr0.le hr1] at h
  rw [intervalIntegral.integral_mul_const] at h
  rw [eq_div_iff hr0.ne']
  exact h

/-- **The scale integral (route item 7).**  For `0 ≤ r < 1`,
`∫_0^1 1/√(1 - (t r)²) dt = arcsin r / r ≤ π/2` (with value `1` at `r = 0`). -/
theorem integral_one_div_sqrt_one_sub_sq_mul_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ t in (0 : ℝ)..1, 1 / Real.sqrt (1 - (t * r) ^ 2) ≤ Real.pi / 2 := by
  rcases eq_or_lt_of_le hr0 with h0 | hpos
  · subst h0
    have hone : (fun t : ℝ => 1 / Real.sqrt (1 - (t * 0) ^ 2)) = fun _ => 1 := by
      funext t; simp
    rw [hone, intervalIntegral.integral_const]
    have hpi : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
    simpa using hpi.le
  · rw [integral_one_div_sqrt_one_sub_sq_mul hpos hr1, div_le_iff₀ hpos]
    exact arcsin_le_pi_div_two_mul hr0 hr1.le

/-- **The scale integral in the route's rpow form.**  For `0 ≤ r < 1`,
`∫_0^1 (1 - (t r)²)^{-1/2} dt ≤ π/2`. -/
theorem integral_one_sub_sq_rpow_neg_half_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ t in (0 : ℝ)..1, (1 - (t * r) ^ 2) ^ (-(1 / 2 : ℝ)) ≤ Real.pi / 2 := by
  have hcongr : ∫ t in (0 : ℝ)..1, (1 - (t * r) ^ 2) ^ (-(1 / 2 : ℝ))
      = ∫ t in (0 : ℝ)..1, 1 / Real.sqrt (1 - (t * r) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    change (1 - (t * r) ^ 2) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt (1 - (t * r) ^ 2)
    exact rpow_neg_half_eq_one_div_sqrt (by
      nlinarith [mul_nonneg ht.1 hr0, mul_le_of_le_one_left hr0 ht.2,
        sq_nonneg (t * r), hr0, hr1])
  rw [hcongr]
  exact integral_one_div_sqrt_one_sub_sq_mul_le hr0 hr1

/-! ### The remaining quantitative input, recorded as a named `Prop`

This is the declaration the Li--Shao route still needs (route item 1).  It is a
statement, not a proof: a `def : Prop`, so the file stays sorry-free while making
the remaining obligation precise. -/

/-- **Route item 1 (the density).**  The density of a nondegenerate centred
multivariate Gaussian `N(0, S)` on `EuclideanSpace ℝ (Fin n)`. -/
def multivariateGaussianDensityFormula : Prop :=
  ∀ (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ), S.PosDef →
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S
      = (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity fun x => ENNReal.ofReal
          ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (S.det) ^ (-(1 : ℝ) / 2) *
            Real.exp (-(x ⬝ᵥ (S⁻¹ *ᵥ x)) / 2))

end LatticeProb
