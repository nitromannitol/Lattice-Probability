/-
Normal comparison: the final bound from the endpoint limit and interpolation.

The density, scalar-covariance and starting-value identities are imported.
The retained theorem supplies the proved starting value to the endpoint form
and leaves hlim and hinterp as its explicit hypotheses.
-/
import LatticeProb.Prob.NormalComparisonFinal
import LatticeProb.Prob.NormalComparisonCovariance
import LatticeProb.Prob.GaussCovDensityScalar
import LatticeProb.Prob.NormalComparisonLimit

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal Matrix

namespace LatticeProb

/-- **The final bound from the remaining two route facts.**  The density/scale step `F 0` is
discharged by `integral_orthant_smartPath_zero`; the hypotheses are the endpoint continuity
`hlim` and the interpolation `hinterp`. -/
theorem normalComparison_bound_of_limit_and_interpolation {m : ℕ} {v : ℝ≥0} (hv : 0 < v)
    {S : Matrix (Fin m) (Fin m) ℝ} (hnonneg : ∀ i j, 0 ≤ S i j) (b : Fin m → ℝ)
    (hlim : Tendsto
      (fun t : ℝ => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S t) x)
      (𝓝[<] 1)
      (𝓝 (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S
        {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i}).toReal))
    (hinterp : ∀ T ∈ Set.Ico (0 : ℝ) 1,
      (∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S 0) x)
          ≤ ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S T) x ∧
        (∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S T) x)
          - (∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S 0) x)
        ≤ ∑ i, ∑ j ∈ Finset.Ioi i, S i j *
            ((4 * (v : ℝ))⁻¹ * Real.exp (-(b i ^ 2 + b j ^ 2) /
              (2 * (v : ℝ) * (1 + T * (S i j / (v : ℝ))))))) :
    |(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S
          {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i}).toReal -
        ∏ i, (gaussianReal 0 v (Set.Iic (b i))).toReal| ≤
      (1 / 4) * ∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
        S i j / (v : ℝ) *
          Real.exp (-(b i ^ 2 + b j ^ 2) / (2 * (v : ℝ) * (1 + S i j / (v : ℝ)))) :=
  normalComparison_bound_of_interpolation_of_endpoints (S := S) hv hnonneg b
    (integral_orthant_smartPath_zero hv b) hlim hinterp

end LatticeProb
