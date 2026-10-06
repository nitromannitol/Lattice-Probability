/-
# Li--Shao normal comparison: the endpoint limit step and the raw final bound

Continuing `LatticeProb/Prob/NormalComparisonFinalFour.lean`'s predecessor
`LatticeProb/Prob/NormalComparisonFinalThree.lean`.  The bound
`normalComparison_bound_of_orthant_raw` takes the left-continuity
`hlim : ∫_{Iic b} covDensity S_t → P(N(0,S) ≤ b)` as a hypothesis.  This file discharges that
**limit step** from the endpoint convergence of the orthant probabilities
(`tendsto_multivariateGaussian_orthant_path`, taken as the analytic input), using the
density/law identification `multivariateGaussian_orthant_toReal_eq` already proved for the route.
The re-assembled bound has the route's final unconditional-shaped form with the endpoint
convergence as its only remaining limit hypothesis.

No `External` is touched, no `Prop` is frozen, and nothing is claimed about `Rotor.External.LSS`.
-/
import LatticeProb.Prob.NormalComparisonFinalThree

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal Matrix

namespace LatticeProb

/-- **The endpoint limit step.**  If the orthant probabilities `P(N(0, S_t) ≤ b)` converge to
`P(N(0, S) ≤ b)` as `t ↑ 1`, then the density integrals `∫_{Iic b} covDensity S_t` do too: for
`t ∈ (0, 1)` the smart path is positive definite, so the density integral equals the orthant
probability by `multivariateGaussian_orthant_toReal_eq`, and the two families are eventually
equal along `𝓝[<] 1`. -/
theorem tendsto_integral_orthant_smartPath_of_endpoint {m : ℕ} {v : ℝ} (hv : 0 < v)
    {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosSemidef) (b : Fin m → ℝ)
    (hend : Tendsto
      (fun t : ℝ => (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (normalComparisonSmartPath v S t)
          {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i}).toReal)
      (𝓝[<] 1)
      (𝓝 ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S
        {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i}).toReal))) :
    Tendsto (fun t : ℝ => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath v S t) x)
      (𝓝[<] 1)
      (𝓝 ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S
        {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i}).toReal)) := by
  refine hend.congr' ?_
  refine eventuallyEq_of_mem (Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)) ?_
  intro t ht
  exact multivariateGaussian_orthant_toReal_eq
    (normalComparisonSmartPath_posDef hS hv ⟨ht.1.le, ht.2⟩) b

/-- **The route's final bound with the endpoint step.**  Same conclusion as
`normalComparison_bound_of_orthant_raw`, but the limit hypothesis is the endpoint convergence
`hend` of the orthant probabilities rather than the density-integral limit; the latter is
discharged by `tendsto_integral_orthant_smartPath_of_endpoint`.  The hypotheses `hcont`, `hraw`,
`hpartial` are the route's continuity, raw-derivative and density inputs, and `hS`, `hdiag`,
`hnonneg` are the paper's smart-path setting. -/
theorem normalComparison_bound_of_orthant_endpoint {m : ℕ} {v : ℝ≥0} (hv : 0 < v)
    {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosSemidef) (hdiag : ∀ i, S i i = (v : ℝ))
    (hnonneg : ∀ i j, 0 ≤ S i j) (b : Fin m → ℝ)
    (hend : Tendsto
      (fun t : ℝ => (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (normalComparisonSmartPath (v : ℝ) S t)
          {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i}).toReal)
      (𝓝[<] 1)
      (𝓝 ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S
        {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i}).toReal)))
    (hcont : ∀ T ∈ Set.Ico (0 : ℝ) 1, ContinuousOn
      (fun t : ℝ => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S t) x)
      (Set.Icc 0 T))
    (hraw : ∀ T ∈ Set.Ico (0 : ℝ) 1, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt
        (fun t : ℝ => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S t) x)
        (1 / 2 * ∑ i, ∑ j, (S - (v : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ)) i j *
          orthantPartial2 (normalComparisonSmartPath (v : ℝ) S t) b i j) t)
    (hpartial : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ i j, i ≠ j →
      0 ≤ orthantPartial2 (normalComparisonSmartPath (v : ℝ) S t) b i j ∧
        orthantPartial2 (normalComparisonSmartPath (v : ℝ) S t) b i j
          ≤ bivariateGaussDensity (v : ℝ) (t * (S i j / (v : ℝ))) (b i) (b j)) :
    |(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S
          {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i}).toReal -
        ∏ i, (gaussianReal 0 v (Set.Iic (b i))).toReal| ≤
      (1 / 4) * ∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
        S i j / (v : ℝ) *
          Real.exp (-(b i ^ 2 + b j ^ 2) / (2 * (v : ℝ) * (1 + S i j / (v : ℝ)))) := by
  refine normalComparison_bound_of_orthant_raw hv hS hdiag hnonneg b ?_ hcont hraw hpartial
  exact tendsto_integral_orthant_smartPath_of_endpoint (NNReal.coe_pos.mpr hv) hS b hend

end LatticeProb
