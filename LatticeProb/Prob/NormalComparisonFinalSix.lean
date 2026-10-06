/-
Normal comparison: the boundary bound from a marginal estimate.

The corner map and nonnegativity of its density integral are imported.
The retained theorem derives the bivariate boundary bound from the explicit
marginal-estimate hypothesis hmarg.
-/
import LatticeProb.Prob.NormalComparisonFinalFive
import LatticeProb.Prob.GaussCovDensityOrthant

open MeasureTheory Matrix

namespace LatticeProb

/-- **Route item 5 from the marginal fact.**  Given the marginal bound `hmarg` for the `2 × 2`
corner density, the boundary integral of `covDensity S_t` along `pairCorner σ b` is nonnegative
and at most the bivariate density at correlation `t * S (σ 0) (σ 1) / v`.  The `2 × 2` submatrix
of the smart path is `!![v, c; c, v]` with `c = t * S (σ 0) (σ 1)`, and `covDensity_two_cov`
identifies its density with `bivariateGaussDensity v (c / v)`. -/
theorem boundary_covDensity_path_le_of_marginal {m : ℕ} {v : ℝ}
    {S : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ} (hv : 0 < v) (hS : S.PosSemidef)
    (hdiag : ∀ i, S i i = v) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (hmarg : ∀ (σ : Equiv.Perm (Fin (m + 2))) (b : Fin (m + 2) → ℝ),
      ∫ x'' in Set.Iic (fun k : Fin m => b (σ k.succ.succ)),
          covDensity (normalComparisonSmartPath v S t) (pairCorner σ b x'')
        ≤ covDensity (!![normalComparisonSmartPath v S t (σ 0) (σ 0),
              normalComparisonSmartPath v S t (σ 0) (σ 1);
              normalComparisonSmartPath v S t (σ 1) (σ 0),
              normalComparisonSmartPath v S t (σ 1) (σ 1)] : Matrix (Fin 2) (Fin 2) ℝ)
            ![b (σ 0), b (σ 1)])
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
  refine (hmarg σ b).trans ?_
  rw [hmat, covDensity_two_cov hv hc]

end LatticeProb
