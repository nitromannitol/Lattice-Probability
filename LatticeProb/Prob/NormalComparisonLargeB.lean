/-
# Li--Shao normal comparison: the large-threshold regime

The headline inequality `LatticeProb.normalComparison_bound` (`NormalComparisonFinal.lean`)
bounds the orthant-comparison error, for **every** threshold vector `b`, by

  `(1/4) ∑_{i<j} (S i j / v) exp (-(b_i² + b_j²) / (2 v (1 + S i j / v)))` .

In its intended application (`sandpile.tex`, Step 1 of `lem:dgt4-path-survival`) the thresholds
are *large*: the Gaussian tail inversion makes each threshold satisfy `b_x² ≍ 4 Var(J) log R`.
This file records the resulting corollary: once every threshold exceeds `R` in absolute value,
the bound no longer depends on `b` at all, so the comparison error is *uniform* over all such
threshold vectors and decays like `exp (-R² /(v (1 + ρ)))`.

  `|N(0,S)(orthant b) − ∏ᵢ N(0,v)(Iic bᵢ)| ≤ (1/4) ∑_{i<j} (S i j / v)
     exp (-(R² + R²) / (2 v (1 + S i j / v)))`  for every `b` with `|b_i| ≥ R`.

## Named gap

The complementary bounded regime `|b_i| ≤ R` is where the pair sum must be controlled by the
**correlation structure** (`S i j` small for distant pairs), and the assembly of the
path-threshold factorization `eq:dgt4-path-threshold-factorization` are outside this module: they
need the scenery field `J` and its correlation gap/decay, so they belong to the application, not
to the library.  The `R → ∞` limit of the right-hand side (each pair term decaying like
`exp (-(2 R²)/(2 v (1 + ρ)))`) is also not formalised here.
-/
import Mathlib
import LatticeProb.Prob.NormalComparisonFinal

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LatticeProb

/-- **The large-threshold form of the normal comparison inequality.**  For a centred Gaussian with
covariance `S`, common variance `v > 0` and nonnegative correlations, if every threshold is at
least `R` in absolute value (`0 ≤ R`), the orthant-comparison error is at most the pair sum with
`b_i²` and `b_j²` both replaced by `R²`.  In particular the bound is uniform in the individual
thresholds `b_i`, and the `b`-dependence enters only through the single parameter `R`. -/
theorem normalComparison_bound_large {m : ℕ} {v : ℝ≥0} (hv : 0 < v)
    {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosSemidef) (hdiag : ∀ i, S i i = (v : ℝ))
    (hnonneg : ∀ i j, 0 ≤ S i j) {R : ℝ} (hR : 0 ≤ R) {b : Fin m → ℝ}
    (hb : ∀ i, R ≤ |b i|) :
    |(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S
          {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i}).toReal -
        ∏ i, (gaussianReal 0 v (Set.Iic (b i))).toReal| ≤
      (1 / 4) * ∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
        S i j / (v : ℝ) *
          Real.exp (-(R ^ 2 + R ^ 2) / (2 * (v : ℝ) * (1 + S i j / (v : ℝ)))) := by
  have hvi : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr hv
  refine (normalComparison_bound hv hS hdiag hnonneg b).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (hnonneg i j) hvi.le)
  refine Real.exp_le_exp.mpr ?_
  have hi : R ^ 2 ≤ b i ^ 2 := by
    rw [← sq_abs R, ← sq_abs (b i)]
    exact pow_le_pow_left₀ (abs_nonneg R) (by simpa [abs_of_nonneg hR] using hb i) 2
  have hj : R ^ 2 ≤ b j ^ 2 := by
    rw [← sq_abs R, ← sq_abs (b j)]
    exact pow_le_pow_left₀ (abs_nonneg R) (by simpa [abs_of_nonneg hR] using hb j) 2
  have hden : 0 < 2 * (v : ℝ) * (1 + S i j / (v : ℝ)) := by
    have : 0 ≤ S i j / (v : ℝ) := div_nonneg (hnonneg i j) hvi.le
    positivity
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_right (by linarith) hden.le

end LatticeProb

#print axioms LatticeProb.normalComparison_bound_large
