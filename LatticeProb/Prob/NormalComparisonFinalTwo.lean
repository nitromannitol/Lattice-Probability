/-
# Li--Shao normal comparison: the final bound from the orthant pieces

Continuing `LatticeProb/Prob/NormalComparisonOrthantFinal.lean`.  The interpolation
`orthant_path_bound_of_pieces` bounds the increase of the orthant integral `F t` along the smart
path in terms of the bivariate density.  This file assembles it with the density/scale starting
value `integral_orthant_smartPath_zero` and the endpoint continuity into the route's **final
normal-comparison bound**

  `|P(N(0,S) ≤ b) - ∏ᵢ P(N(0,v) ≤ bᵢ)|
      ≤ (1/4) ∑ᵢ ∑_{j > i} (Sᵢⱼ/v) exp (-(bᵢ²+bⱼ²)/(2v(1+Sᵢⱼ/v)))`.

The remaining route facts are taken as hypotheses: the left-continuity at `t = 1` (`hlim`) and
the three pointwise analytic inputs of the orthant step (`hcont`, `hderiv`, `hpartial`).  No
`External` is touched and no `Prop` is frozen.
-/
import LatticeProb.Prob.NormalComparisonOrthantFinal
import LatticeProb.Prob.NormalComparisonAssembly

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal Matrix

namespace LatticeProb

/-- **The interpolation from the orthant pieces.**  Packaging `orthant_path_bound_of_pieces` at
each `T ∈ [0, 1)` (and `T = 0`) yields the interpolation hypothesis consumed below by
`normalComparison_bound_of_limit_and_interpolation`. -/
theorem normalComparison_interpolation_of_orthant_pieces {m : ℕ} {v : ℝ≥0} (hv : 0 < v)
    {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosSemidef) (hdiag : ∀ i, S i i = (v : ℝ))
    (hnonneg : ∀ i j, 0 ≤ S i j) (b : Fin m → ℝ)
    (hcont : ∀ T ∈ Set.Ico (0 : ℝ) 1, ContinuousOn
      (fun t : ℝ => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S t) x)
      (Set.Icc 0 T))
    (hderiv : ∀ T ∈ Set.Ico (0 : ℝ) 1, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt
        (fun t : ℝ => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S t) x)
        (∑ i, ∑ j ∈ Finset.Ioi i, S i j *
          orthantPartial2 (normalComparisonSmartPath (v : ℝ) S t) b i j) t)
    (hpartial : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ i j, i ≠ j →
      0 ≤ orthantPartial2 (normalComparisonSmartPath (v : ℝ) S t) b i j ∧
        orthantPartial2 (normalComparisonSmartPath (v : ℝ) S t) b i j
          ≤ bivariateGaussDensity (v : ℝ) (t * (S i j / (v : ℝ))) (b i) (b j)) :
    ∀ T ∈ Set.Ico (0 : ℝ) 1,
      (∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S 0) x)
          ≤ ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S T) x ∧
        (∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S T) x)
          - (∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S 0) x)
        ≤ ∑ i, ∑ j ∈ Finset.Ioi i, S i j *
            ((4 * (v : ℝ))⁻¹ * Real.exp (-(b i ^ 2 + b j ^ 2) /
              (2 * (v : ℝ) * (1 + T * (S i j / (v : ℝ)))))) :=
  fun T hT => orthant_path_bound_of_pieces (NNReal.coe_pos.mpr hv) hS hdiag hnonneg b hT
    (hcont T hT) (hderiv T hT) hpartial

/-- **The route's final normal-comparison bound.**  Combining the orthant interpolation, the
density/scale starting value `integral_orthant_smartPath_zero` and the endpoint continuity `hlim`
gives the normal comparison inequality with constant `1/4`.  The hypotheses `hS`, `hdiag`,
`hnonneg` are the smart-path hypotheses, and `hlim`, `hcont`, `hderiv`, `hpartial` are the
remaining route facts. -/
theorem normalComparison_bound_of_orthant_pieces {m : ℕ} {v : ℝ≥0} (hv : 0 < v)
    {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosSemidef) (hdiag : ∀ i, S i i = (v : ℝ))
    (hnonneg : ∀ i j, 0 ≤ S i j) (b : Fin m → ℝ)
    (hlim : Tendsto
      (fun t : ℝ => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S t) x)
      (𝓝[<] 1)
      (𝓝 (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S
        {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i}).toReal))
    (hcont : ∀ T ∈ Set.Ico (0 : ℝ) 1, ContinuousOn
      (fun t : ℝ => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S t) x)
      (Set.Icc 0 T))
    (hderiv : ∀ T ∈ Set.Ico (0 : ℝ) 1, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt
        (fun t : ℝ => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S t) x)
        (∑ i, ∑ j ∈ Finset.Ioi i, S i j *
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
  refine normalComparison_bound_of_limit_and_interpolation (S := S) hv hnonneg b hlim ?_
  exact normalComparison_interpolation_of_orthant_pieces hv hS hdiag hnonneg b hcont hderiv hpartial

end LatticeProb
