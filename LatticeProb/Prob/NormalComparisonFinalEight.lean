/-
# Li--Shao normal comparison: route items 4 and 5, and the density-fed final bound

Continuing `LatticeProb/Prob/NormalComparisonFinalSix.lean`.  The mixed-partial orthant integral
`orthantPartial2 M b i j` on the smart path lies between `0` and the bivariate density at
correlation `t S i j / v` (route items 4 and 5).  This file assembles that bound from its two
route facts, taken as hypotheses: the boundary decomposition `h4` (the mixed-partial orthant
integral equals the corner integral of `covDensity` along `pairCorner σ b`) and the boundary bound
`h5` of the corner integral by the pair density
`bivariateGaussDensity v (t S (σ 0) (σ 1) / v) (b (σ 0)) (b (σ 1))`.  It then re-assembles the
route's final bound with the density hypothesis discharged.

No `External` is touched, no `Prop` is frozen, and nothing is claimed about `Rotor.External.LSS`.
-/
import LatticeProb.Prob.NormalComparisonFinalFour
import LatticeProb.Prob.NormalComparisonFinalSix
import LatticeProb.Prob.NormalComparisonOrthantFinal

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal Matrix

namespace LatticeProb

/-- **Route items 4 and 5, assembled from the two boundary facts.**  Given the mixed-partial
boundary decomposition `h4` and the corner bound `h5`, the orthant integral of the mixed second
partial on the smart path is nonnegative and at most the bivariate density at correlation
`t S i j / v`. -/
theorem orthantPartial2_nonneg_le_of_boundary {m : ℕ} {v : ℝ}
    {S : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ} {t : ℝ} (b : Fin (m + 2) → ℝ)
    {i j : Fin (m + 2)}
    (h4 : ∃ σ : Equiv.Perm (Fin (m + 2)), σ 0 = i ∧ σ 1 = j ∧
      orthantPartial2 (normalComparisonSmartPath v S t) b i j
        = ∫ x'' in Set.Iic (fun k : Fin m => b (σ k.succ.succ)),
            covDensity (normalComparisonSmartPath v S t) (pairCorner σ b x''))
    (h5 : ∀ σ : Equiv.Perm (Fin (m + 2)),
      0 ≤ ∫ x'' in Set.Iic (fun k : Fin m => b (σ k.succ.succ)),
            covDensity (normalComparisonSmartPath v S t) (pairCorner σ b x'') ∧
        ∫ x'' in Set.Iic (fun k : Fin m => b (σ k.succ.succ)),
            covDensity (normalComparisonSmartPath v S t) (pairCorner σ b x'')
          ≤ bivariateGaussDensity v (t * S (σ 0) (σ 1) / v) (b (σ 0)) (b (σ 1))) :
    0 ≤ orthantPartial2 (normalComparisonSmartPath v S t) b i j ∧
      orthantPartial2 (normalComparisonSmartPath v S t) b i j
        ≤ bivariateGaussDensity v (t * (S i j / v)) (b i) (b j) := by
  obtain ⟨σ, h0, h1, heq⟩ := h4
  obtain ⟨hlo, hhi⟩ := h5 σ
  rw [h0, h1] at hhi
  rw [heq]
  refine ⟨hlo, ?_⟩
  rw [mul_div_assoc] at hhi
  exact hhi

/-- **The route's final bound with the density step discharged.**  Same conclusion as
`normalComparison_bound_of_orthant_endpoint`, but the density hypothesis `hpartial` is supplied
from the two route facts `h4` and `h5` by `orthantPartial2_nonneg_le_of_boundary`; the remaining
inputs are the endpoint convergence `hend`, the path continuity `hcont`, the raw derivative
`hraw`, and the smart-path setting `hS`, `hdiag`, `hnonneg`. -/
theorem normalComparison_bound_of_orthant_density {m : ℕ} {v : ℝ≥0} (hv : 0 < v)
    {S : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ} (hS : S.PosSemidef)
    (hdiag : ∀ i, S i i = (v : ℝ)) (hnonneg : ∀ i j, 0 ≤ S i j) (b : Fin (m + 2) → ℝ)
    (hend : Tendsto
      (fun t : ℝ => (multivariateGaussian (0 : EuclideanSpace ℝ (Fin (m + 2)))
        (normalComparisonSmartPath (v : ℝ) S t)
          {y : EuclideanSpace ℝ (Fin (m + 2)) | ∀ i, y i ≤ b i}).toReal)
      (𝓝[<] 1)
      (𝓝 ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin (m + 2))) S
        {y : EuclideanSpace ℝ (Fin (m + 2)) | ∀ i, y i ≤ b i}).toReal)))
    (hcont : ∀ T ∈ Set.Ico (0 : ℝ) 1, ContinuousOn
      (fun t : ℝ => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S t) x)
      (Set.Icc 0 T))
    (hraw : ∀ T ∈ Set.Ico (0 : ℝ) 1, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt
        (fun t : ℝ => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S t) x)
        (1 / 2 * ∑ i, ∑ j, (S - (v : ℝ) • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ)) i j *
          orthantPartial2 (normalComparisonSmartPath (v : ℝ) S t) b i j) t)
    (h4 : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ {i j : Fin (m + 2)}, i ≠ j →
      ∃ σ : Equiv.Perm (Fin (m + 2)), σ 0 = i ∧ σ 1 = j ∧
        orthantPartial2 (normalComparisonSmartPath (v : ℝ) S t) b i j
          = ∫ x'' in Set.Iic (fun k : Fin m => b (σ k.succ.succ)),
              covDensity (normalComparisonSmartPath (v : ℝ) S t) (pairCorner σ b x''))
    (h5 : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ σ : Equiv.Perm (Fin (m + 2)),
      0 ≤ ∫ x'' in Set.Iic (fun k : Fin m => b (σ k.succ.succ)),
            covDensity (normalComparisonSmartPath (v : ℝ) S t) (pairCorner σ b x'') ∧
        ∫ x'' in Set.Iic (fun k : Fin m => b (σ k.succ.succ)),
            covDensity (normalComparisonSmartPath (v : ℝ) S t) (pairCorner σ b x'')
          ≤ bivariateGaussDensity (v : ℝ) (t * S (σ 0) (σ 1) / (v : ℝ)) (b (σ 0)) (b (σ 1))) :
    |(multivariateGaussian (0 : EuclideanSpace ℝ (Fin (m + 2))) S
          {y : EuclideanSpace ℝ (Fin (m + 2)) | ∀ i, y i ≤ b i}).toReal -
        ∏ i, (gaussianReal 0 v (Set.Iic (b i))).toReal| ≤
      (1 / 4) * ∑ i : Fin (m + 2), ∑ j ∈ Finset.Ioi i,
        S i j / (v : ℝ) *
          Real.exp (-(b i ^ 2 + b j ^ 2) / (2 * (v : ℝ) * (1 + S i j / (v : ℝ)))) := by
  refine normalComparison_bound_of_orthant_endpoint hv hS hdiag hnonneg b hend hcont hraw ?_
  intro t ht i j hij
  exact orthantPartial2_nonneg_le_of_boundary b (h4 t ht hij) (h5 t ht)

end LatticeProb
