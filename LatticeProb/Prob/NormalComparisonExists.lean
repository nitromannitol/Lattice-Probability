import LatticeProb.Prob.NormalComparisonLimit
import LatticeProb.Prob.NormalComparisonInterpolation

/-!
# The normal comparison inequality

The smart-path interpolation and its singular endpoint limit give a uniform bound for
all dimensions and all nonnegative positive-semidefinite constant-diagonal covariances.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProb

/-- The normal comparison inequality for Gaussian orthants with nonnegative correlations. -/
theorem normalComparison_exists :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ) (v : ℝ≥0), 0 < v →
        ∀ S : Matrix (Fin m) (Fin m) ℝ, S.PosSemidef →
          (∀ i, S i i = (v : ℝ)) → (∀ i j, 0 ≤ S i j) →
          ∀ b : Fin m → ℝ,
            |(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S
                    {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i}).toReal -
                ∏ i, (gaussianReal 0 v (Set.Iic (b i))).toReal| ≤
              C * ∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
                S i j / (v : ℝ) *
                  Real.exp (-(b i ^ 2 + b j ^ 2) /
                    (2 * (v : ℝ) * (1 + S i j / (v : ℝ)))) := by
  refine ⟨(1 / 4 : ℝ), by norm_num, ?_⟩
  intro m v hv S hS hdiag hnonneg b
  exact normalComparison_bound_of_interpolation hv hS hdiag hnonneg b
    (fun T hT => orthant_path_interpolation (NNReal.coe_pos.mpr hv)
      hS hdiag hnonneg b hT)

end LatticeProb
