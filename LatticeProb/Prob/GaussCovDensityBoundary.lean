/-
# The boundary integral along the smart path (route item 5)

Li--Shao normal comparison (`scratch/pk/normalcompare-route.md`, item 5).  Let `S` be a positive
semidefinite matrix with constant diagonal `v > 0`, and `S_t = (1 - t) • (v • 1) + t • S` the smart
path (`LatticeProb/Prob/NormalComparison.lean`).  For `t ∈ [0, 1)` the matrix `S_t` is positive
definite, and the boundary integral of `covDensity S_t` over the orthant of the remaining
coordinates at the corner point `pairCorner σ b` (`integral_Iic_partial2_covDensity` of
`LatticeProb/Prob/GaussCovDensityOrthant.lean`) is nonnegative and at most the bivariate Gaussian
density at variance `v` and correlation `t * S (σ 0) (σ 1) / v`.

## Route

* `abs_apply_le_of_posSemidef_diag`: the quadratic form of `S` at `e_i ± e_j` is nonnegative, which
  gives `2 v ± 2 S i j ≥ 0`.
* `boundary_covDensity_path_le`: the marginal bound `integral_Iic_pairCorner_covDensity_le`
  (`LatticeProb/Prob/GaussCovDensityMarginal.lean`) reduces the boundary integral to the `2 × 2`
  density, whose matrix is `!![v, c; c, v]` with `c = t * S (σ 0) (σ 1)` and `|c| < v`, so
  `covDensity_two_cov` (`LatticeProb/Prob/GaussCovDensityTwo.lean`) identifies it with
  `bivariateGaussDensity v (c / v)`.
-/
import Mathlib
import LatticeProb.Prob.GaussCovDensityMarginal
import LatticeProb.Prob.GaussCovDensityTwo
import LatticeProb.Prob.GaussCovDensityOrthant
import LatticeProb.Prob.NormalComparisonPath
import LatticeProb.Prob.NormalComparisonBoundary

open MeasureTheory Matrix

namespace LatticeProb

section Boundary

variable {m : ℕ} {v : ℝ} {S : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ}

/-- The quadratic form of a positive semidefinite real matrix at `e_i + s • e_j` with
`i ≠ j` is nonnegative: `0 ≤ S i i + s (S i j + S j i) + s ^ 2 S j j`. -/
private theorem quad_pair_nonneg (hS : S.PosSemidef) {i j : Fin (m + 2)} (s : ℝ) :
    0 ≤ S i i + s * (S i j + S j i) + s ^ 2 * S j j := by
  have h := hS.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j s)
  simp [dotProduct_add, mulVec_add] at h
  linarith

/-- A positive semidefinite matrix with constant diagonal `v` has entries bounded by `v`. -/
theorem abs_apply_le_of_posSemidef_diag_add_two (hv : 0 < v) (hS : S.PosSemidef)
    (hdiag : ∀ i, S i i = v) (i j : Fin (m + 2)) : |S i j| ≤ v := by
  by_cases hij : i = j
  · subst hij
    rw [hdiag i, abs_of_pos hv]
  · have hsym : S j i = S i j := by
      simpa using hS.isHermitian.apply i j
    have h1 := quad_pair_nonneg hS (i := i) (j := j) 1
    have h2 := quad_pair_nonneg hS (i := i) (j := j) (-1)
    rw [hdiag i, hdiag j, hsym] at h1 h2
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **Route item 5.**  At each point `t ∈ [0,1)` of the smart path, the boundary integral of the
density is nonnegative and at most the bivariate density at correlation `t * S (σ 0) (σ 1) / v`. -/
theorem boundary_covDensity_path_le (hv : 0 < v) (hS : S.PosSemidef)
    (hdiag : ∀ i, S i i = v) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (σ : Equiv.Perm (Fin (m + 2))) (b : Fin (m + 2) → ℝ) :
    0 ≤ ∫ x'' in Set.Iic (fun k : Fin m => b (σ k.succ.succ)),
        covDensity (normalComparisonSmartPath v S t) (pairCorner σ b x'')
    ∧ ∫ x'' in Set.Iic (fun k : Fin m => b (σ k.succ.succ)),
        covDensity (normalComparisonSmartPath v S t) (pairCorner σ b x'')
      ≤ bivariateGaussDensity v (t * S (σ 0) (σ 1) / v) (b (σ 0)) (b (σ 1)) := by
  have hM := normalComparisonSmartPath_posDef hS hv ht
  have hne : σ 0 ≠ σ 1 := fun h => Fin.zero_ne_one (σ.injective h)
  have hsym : S (σ 1) (σ 0) = S (σ 0) (σ 1) := by
    simpa using hS.isHermitian.apply (σ 0) (σ 1)
  have hc : |t * S (σ 0) (σ 1)| < v := by
    have hb := abs_apply_le_of_posSemidef_diag hv hS hdiag (σ 0) (σ 1)
    rw [abs_mul, abs_of_nonneg ht.1]
    nlinarith [ht.1, ht.2, abs_nonneg (S (σ 0) (σ 1))]
  have hmat : (!![normalComparisonSmartPath v S t (σ 0) (σ 0),
        normalComparisonSmartPath v S t (σ 0) (σ 1);
        normalComparisonSmartPath v S t (σ 1) (σ 0),
        normalComparisonSmartPath v S t (σ 1) (σ 1)] : Matrix (Fin 2) (Fin 2) ℝ)
      = !![v, t * S (σ 0) (σ 1); t * S (σ 0) (σ 1), v] := by
    rw [normalComparisonSmartPath_diag hdiag, normalComparisonSmartPath_diag hdiag,
      normalComparisonSmartPath_apply_of_ne v S t hne,
      normalComparisonSmartPath_apply_of_ne v S t hne.symm, hsym]
  refine ⟨integral_Iic_pairCorner_covDensity_nonneg hM b σ, ?_⟩
  refine (integral_Iic_pairCorner_covDensity_le hM σ b).trans ?_
  rw [hmat, covDensity_two_cov hv hc]

end Boundary

end LatticeProb
