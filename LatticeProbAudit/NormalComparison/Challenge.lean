import Mathlib

/-!
# The normal comparison inequality: comparator challenge

Mathlib-only comparator challenge for the normal comparison inequality of Li and Shao
(*Probability Theory and Related Fields* 122 (2002), Corollary 2.1), specialised to nonnegative
correlations, `LatticeProb.normalComparison_exists` in
`LatticeProb/Prob/NormalComparisonFinal.lean`.

Content: there is a constant `C > 0` such that, for every dimension `m`, every variance `v > 0`,
every positive semidefinite `m × m` matrix `S` with constant diagonal `v` and nonnegative entries,
and every `b : Fin m → ℝ`, the probability that a centred Gaussian vector with covariance `S` lies
in the orthant `{y | ∀ i, y i ≤ b i}` differs from the product of the one-dimensional probabilities
`P(N(0, v) ≤ b i)` by at most
`C ∑_{i<j} (S i j / v) exp (-(b i² + b j²) / (2 v (1 + S i j / v)))`.

Only Mathlib is imported, and no definition is needed: the Gaussian laws are Mathlib's
`multivariateGaussian` and `gaussianReal`. The sole intentional `sorry` is the proof of the final
theorem.

## Presentation deltas

None: the statement is the body of the cited proposition, unchanged.  The library proves it with
`C = 1/4`.
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
  sorry

end LatticeProbAudit
