/-
# Li-Shao normal comparison: bounds for the mixed-partial orthant integrals

Route items 4 and 5 combined.  On the smart path `normalComparisonSmartPath v S t` with
`t ∈ [0, 1)`, the orthant integral `orthantPartial2 M b i j` of the mixed second partial of the
Gaussian density equals (`integral_Iic_partial2_covDensity`) the boundary integral of the density
along `pairCorner σ b`, which is nonnegative and at most the bivariate Gaussian density at
correlation `t * S i j / v` (`boundary_covDensity_path_le`).

## Main results

* `orthantPartial2_nonneg_le`: `0 ≤ orthantPartial2 (normalComparisonSmartPath v S t) b i j` and
  it is at most `bivariateGaussDensity v (t * S i j / v) (b i) (b j)`, for `i ≠ j`.
-/
import Mathlib
import LatticeProb.Prob.GaussCovDensityOrthantPairs
import LatticeProb.Prob.GaussCovDensityBoundary
import LatticeProb.Prob.GaussCovDensityOrthant

open MeasureTheory Matrix

namespace LatticeProb

/-- Route items 4 and 5: on the smart path, each mixed-partial orthant integral lies between `0`
and the bivariate density at correlation `t * S i j / v`. -/
theorem orthantPartial2_nonneg_le {n : ℕ} {v : ℝ} (hv : 0 < v)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) (hdiag : ∀ i, S i i = v)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) (b : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) :
    0 ≤ orthantPartial2 (normalComparisonSmartPath v S t) b i j ∧
      orthantPartial2 (normalComparisonSmartPath v S t) b i j
        ≤ bivariateGaussDensity v (t * S i j / v) (b i) (b j) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := by
    refine ⟨n - 2, ?_⟩
    by_contra hn
    apply hij
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  have hM := normalComparisonSmartPath_posDef hS hv ht
  obtain ⟨σ, h0, h1, heq⟩ := integral_Iic_partial2_covDensity hM hij b
  obtain ⟨hlo, hhi⟩ := boundary_covDensity_path_le hv hS hdiag ht σ b
  rw [h0, h1] at hhi
  have hdef : orthantPartial2 (normalComparisonSmartPath v S t) b i j
      = ∫ x'' in Set.Iic (fun k : Fin m => b (σ k.succ.succ)),
        covDensity (normalComparisonSmartPath v S t) (pairCorner σ b x'') := heq
  rw [hdef]
  exact ⟨hlo, hhi⟩

end LatticeProb
