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
import LatticeProb.Prob.NormalComparisonScaleFinal

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

end LatticeProb
