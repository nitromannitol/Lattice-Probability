/-
# Li--Shao normal comparison: the integrated bivariate contribution

Continuing `LatticeProb/Prob/NormalComparison.lean` (commit `3833332`) and the
route `scratch/pk/normalcompare-route.md`.  The smart-path derivative is a sum of
boundary contributions, one for each pair `i < j`, and after the conditional
factorisation each contribution is at most the bivariate density at the running
correlation `t * r`.  This file lands the integrated form of that bound: the
`t`-average over the smart path of the bivariate density is at most the
frozen pair term.

  `∫_0^1 p_v(t r; a, b) dt ≤ (1 / (2 π v)) · (π / 2) · exp (-(a² + b²) / (2 v (1 + r)))`,

for `0 ≤ r < 1`.  It combines the pointwise density comparison
`bivariateGaussDensity_le` (route item 6) with the scale integral
`integral_one_div_sqrt_one_sub_sq_mul_le` (route item 7).

The remaining inputs of the route are unchanged and named in the module
docstring of `NormalComparison.lean`: the multivariate density
(`multivariateGaussianDensityFormula`), the covariance-derivative of the orthant
probability, and the double integration by parts that identifies it with the
boundary integral.
-/
import LatticeProb.Prob.NormalComparison
import LatticeProb.Prob.NormalComparisonScale

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal MatrixOrder Matrix

namespace LatticeProb

/-- `1 - (t r)² > 0` for `t ∈ [0,1]` and `0 ≤ r < 1`. -/
private theorem one_sub_sq_pos {r t : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 < 1 - (t * r) ^ 2 := by
  have hge : 0 ≤ t * r := mul_nonneg (Set.mem_Icc.mp ht).1 hr0
  have hle : t * r ≤ r := by
    have := mul_le_mul_of_nonneg_right (Set.mem_Icc.mp ht).2 hr0
    simpa using this
  nlinarith [hge, hle, hr1]

/-- The bivariate density at correlation `t * r` is continuous on `[0, 1]`. -/
private theorem continuousOn_bivariateGaussDensity {v r a b : ℝ} (hv : 0 < v) (hr0 : 0 ≤ r)
    (hr1 : r < 1) :
    ContinuousOn (fun t : ℝ => bivariateGaussDensity v (t * r) a b) (Set.Icc (0 : ℝ) 1) := by
  have hden : ContinuousOn (fun t : ℝ => 2 * Real.pi * v * Real.sqrt (1 - (t * r) ^ 2))
      (Set.Icc (0 : ℝ) 1) := by fun_prop
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      2 * Real.pi * v * Real.sqrt (1 - (t * r) ^ 2) ≠ 0 := by
    intro t ht
    exact mul_ne_zero (mul_ne_zero (by positivity) (by positivity))
      (ne_of_gt (Real.sqrt_pos.mpr (one_sub_sq_pos hr0 hr1 ht)))
  have hexp : ContinuousOn (fun t : ℝ => Real.exp
      (-(a ^ 2 - 2 * (t * r) * a * b + b ^ 2) / (2 * v * (1 - (t * r) ^ 2))))
      (Set.Icc (0 : ℝ) 1) := by
    apply Real.continuous_exp.comp_continuousOn
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro t ht
      exact mul_ne_zero (by positivity) (ne_of_gt (one_sub_sq_pos hr0 hr1 ht))
  unfold bivariateGaussDensity
  exact (hden.inv₀ hne).mul hexp

/-- **The integrated bivariate contribution (route items 6 + 7).**  For `0 ≤ r < 1`,
the average over the smart path `t ∈ [0,1]` of the bivariate Gaussian density at
correlation `t * r` is at most the frozen pair term. -/
theorem integral_bivariateGaussDensity_le {v r a b : ℝ} (hv : 0 < v) (hr0 : 0 ≤ r)
    (hr1 : r < 1) :
    ∫ t in (0 : ℝ)..1, bivariateGaussDensity v (t * r) a b
      ≤ (2 * Real.pi * v)⁻¹ * (Real.pi / 2) *
          Real.exp (-(a ^ 2 + b ^ 2) / (2 * v * (1 + r))) := by
  set E : ℝ := Real.exp (-(a ^ 2 + b ^ 2) / (2 * v * (1 + r))) with hE
  have hpoint : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      bivariateGaussDensity v (t * r) a b
        ≤ (2 * Real.pi * v)⁻¹ * (Real.sqrt (1 - (t * r) ^ 2))⁻¹ * E := by
    intro t ht
    have htr0 : 0 ≤ t * r := mul_nonneg (Set.mem_Icc.mp ht).1 hr0
    have htr1 : t * r < 1 := by
      have hle : t * r ≤ r := by
        have := mul_le_mul_of_nonneg_right (Set.mem_Icc.mp ht).2 hr0
        simpa using this
      exact lt_of_le_of_lt hle hr1
    refine (bivariateGaussDensity_le (v := v) (r := t * r) (a := a) (b := b) hv htr0
      htr1).trans ?_
    have hexp : Real.exp (-(a ^ 2 + b ^ 2) / (2 * v * (1 + t * r))) ≤ E := by
      rw [hE]
      apply Real.exp_le_exp.mpr
      have hcmp : (a ^ 2 + b ^ 2) / (2 * v * (1 + r))
          ≤ (a ^ 2 + b ^ 2) / (2 * v * (1 + t * r)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (by nlinarith [mul_le_mul_of_nonneg_right (Set.mem_Icc.mp ht).2 hr0, hr1, hv])
      simpa only [neg_div] using neg_le_neg hcmp
    have hpre : 0 ≤ (2 * Real.pi * v)⁻¹ * (Real.sqrt (1 - (t * r) ^ 2))⁻¹ :=
      mul_nonneg (inv_nonneg.mpr (by positivity)) (inv_nonneg.mpr (Real.sqrt_nonneg _))
    exact mul_le_mul_of_nonneg_left hexp hpre
  have hleft : IntervalIntegrable (fun t : ℝ => bivariateGaussDensity v (t * r) a b) volume 0 1 :=
    ContinuousOn.intervalIntegrable (by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        continuousOn_bivariateGaussDensity hv hr0 hr1)
  have hright : IntervalIntegrable
      (fun t : ℝ => (2 * Real.pi * v)⁻¹ * (Real.sqrt (1 - (t * r) ^ 2))⁻¹ * E) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply ContinuousOn.mul
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.inv₀ (Real.continuous_sqrt.comp_continuousOn (by fun_prop))
      intro t ht
      exact ne_of_gt (Real.sqrt_pos.mpr (one_sub_sq_pos hr0 hr1 ht))
    · exact continuousOn_const
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hleft hright hpoint
  have hscale : ∫ t in (0 : ℝ)..1, (2 * Real.pi * v)⁻¹ * (Real.sqrt (1 - (t * r) ^ 2))⁻¹ * E
      = (2 * Real.pi * v)⁻¹ * E * (∫ t in (0 : ℝ)..1, 1 / Real.sqrt (1 - (t * r) ^ 2)) := by
    rw [show (fun t : ℝ => (2 * Real.pi * v)⁻¹ * (Real.sqrt (1 - (t * r) ^ 2))⁻¹ * E)
        = (fun t : ℝ => ((2 * Real.pi * v)⁻¹ * E) * (1 / Real.sqrt (1 - (t * r) ^ 2))) by
      funext t
      rw [inv_eq_one_div]
      ring]
    rw [intervalIntegral.integral_const_mul]
  calc ∫ t in (0 : ℝ)..1, bivariateGaussDensity v (t * r) a b
      ≤ ∫ t in (0 : ℝ)..1, (2 * Real.pi * v)⁻¹ * (Real.sqrt (1 - (t * r) ^ 2))⁻¹ * E := hmono
    _ = (2 * Real.pi * v)⁻¹ * E * (∫ t in (0 : ℝ)..1, 1 / Real.sqrt (1 - (t * r) ^ 2)) :=
        hscale
    _ ≤ (2 * Real.pi * v)⁻¹ * E * (Real.pi / 2) := by
        refine mul_le_mul_of_nonneg_left (integral_one_div_sqrt_one_sub_sq_mul_le hr0 hr1) ?_
        exact mul_nonneg (inv_nonneg.mpr (by positivity)) (Real.exp_pos _).le
    _ = (2 * Real.pi * v)⁻¹ * (Real.pi / 2) *
          Real.exp (-(a ^ 2 + b ^ 2) / (2 * v * (1 + r))) := by
        rw [hE]; ring

end LatticeProb
