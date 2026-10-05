/-
# The normal comparison inequality of Li and Shao for the orthant

For a centred Gaussian vector with covariance `S`, common variance `v` and nonnegative
correlations `ρ_{ij} = S i j / v`, the probability of an orthant differs from the product of the
one-dimensional probabilities by at most

  `C ∑_{i<j} ρ_{ij} exp (-(b_i² + b_j²) / (2 v (1 + ρ_{ij})))` ,

here with the explicit constant `C = 1/4` (Li and Shao, *Probability Theory and Related Fields*
122 (2002), Corollary 2.1, specialised to nonnegative correlations).

The proof is the smart-path interpolation `S_t = (1 - t) • (v • 1) + t • S`:

* `orthant_path_interpolation` (`NormalComparisonInterpolation.lean`): for every `T < 1` the
  orthant probability of `N(0, S_T)` increases from the product value at `t = 0` by at most the
  sum over pairs of `S i j` times the integrated bivariate density, itself bounded by
  `(4 v)⁻¹ exp (-(b_i² + b_j²) / (2 v (1 + T ρ_{ij})))`;
* `normalComparison_bound_of_interpolation` (`NormalComparisonLimit.lean`): the limit `T → 1`,
  using left-continuity of the orthant probability at the possibly singular endpoint.

`normalComparison_exists` states the result in exactly the shape of the cited proposition, so that
a development holding that proposition as a hypothesis can discharge it by this term.
-/
import Mathlib
import LatticeProb.Prob.NormalComparisonInterpolation
import LatticeProb.Prob.NormalComparisonLimit

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb

/-- **The normal comparison inequality** for the orthant, with the constant `1/4`. -/
theorem normalComparison_bound {m : ℕ} {v : ℝ≥0} (hv : 0 < v)
    {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosSemidef) (hdiag : ∀ i, S i i = (v : ℝ))
    (hnonneg : ∀ i j, 0 ≤ S i j) (b : Fin m → ℝ) :
    |(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S
          {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i}).toReal -
        ∏ i, (gaussianReal 0 v (Set.Iic (b i))).toReal| ≤
      (1 / 4) * ∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
        S i j / (v : ℝ) *
          Real.exp (-(b i ^ 2 + b j ^ 2) / (2 * (v : ℝ) * (1 + S i j / (v : ℝ)))) :=
  normalComparison_bound_of_interpolation hv hS hdiag hnonneg b
    (fun _ hT => orthant_path_interpolation (NNReal.coe_pos.mpr hv) hS hdiag hnonneg b hT)

/-- The normal comparison inequality, stated with an existential constant exactly as in the
cited proposition: some `C > 0` works for every dimension, variance, admissible covariance
and orthant. -/
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
                    (2 * (v : ℝ) * (1 + S i j / (v : ℝ)))) :=
  ⟨1 / 4, by norm_num, fun _ _ hv _ hS hdiag hnonneg b =>
    normalComparison_bound hv hS hdiag hnonneg b⟩

end LatticeProb
