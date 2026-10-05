import Mathlib
import LatticeProb.Prob.NormalComparisonFinal

/-!
# Solution: NormalComparison

The challenge module `LatticeProbAudit/NormalComparison/Challenge.lean` imports only Mathlib and
states the normal comparison inequality with one intentional `sorry`.  This solution proves the
byte-identical statement by `LatticeProb.normalComparison_exists`, whose statement is the
challenge's.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProbAudit

/-- **The normal comparison inequality** for the orthant, nonnegative correlations. -/
theorem normal_comparison :
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
  exact LatticeProb.normalComparison_exists

end LatticeProbAudit
