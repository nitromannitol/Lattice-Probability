/-
# The orthant integral of the mixed second partial of the Gaussian density (route item 4)

Li--Shao normal comparison (`scratch/pk/normalcompare-route.md`, item 4).  For a positive definite
`S` and the density `p = covDensity S` of `N(0, S)` on `Fin (m+2) → ℝ`
(`LatticeProb/Prob/GaussCovDensity.lean`), the coordinate partials are

  `∂_i p = -(S⁻¹ x)_i p`,    `∂_j ∂_i p = ((S⁻¹ x)_i (S⁻¹ x)_j - S⁻¹ i j) p`.

This file assembles the general-coordinate mixed-derivative orthant integral
`LatticeProb.exists_perm_integral_Iic_mixed_deriv`
(`LatticeProb/Prob/NormalComparisonOrthantPair.lean`) with the one-variable differentiation and
decay lemmas of `LatticeProb/Prob/GaussCovDensityPartials.lean` and the global integrability of
`LatticeProb/Prob/GaussCovDensityIntegrable.lean`.

## Route

Apply `exists_perm_integral_Iic_mixed_deriv i j hij b p px pxy` with `p := covDensity S`,
`px x := -(S⁻¹ x)_i p x` and `pxy x := ((S⁻¹ x)_i (S⁻¹ x)_j - S⁻¹ i j) p x`.  Its six side
conditions are, verbatim after `beta` reduction,

* `hdy`: `hasDerivAt_covDensity_partial_update` (the derivative of `px` along `update y j s`);
* `hdy_int`: `integrable_partial2_covDensity_update`;
* `hdy_lim`: `tendsto_partial_covDensity_update_atBot`;
* `hdx`: `hasDerivAt_covDensity_update` (the derivative of `p` along `update y i s`);
* `hdx_int`: `integrable_partial_covDensity_update` with `(i, j) := (i, i)`;
* `hlim`: `tendsto_covDensity_update_atBot`;

and the global hypothesis `hint` is `integrable_partial2_covDensity`.  The boundary integral is
nonnegative because `covDensity S` is positive (`covDensity_pos`).
-/
import Mathlib
import LatticeProb.Prob.GaussCovDensity
import LatticeProb.Prob.GaussCovDensityPartials
import LatticeProb.Prob.GaussCovDensityIntegrable
import LatticeProb.Prob.NormalComparisonOrthantPair

open MeasureTheory Matrix

namespace LatticeProb

section Orthant

variable {m : ℕ} {S : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ}

/-- **Route item 4 for the Gaussian density.**  The orthant integral of the mixed second partial
`∂_i ∂_j p = ((S⁻¹x)_i (S⁻¹x)_j - S⁻¹ i j) p` of `p = covDensity S` over `{x ≤ b}` equals the
integral of `p` at the corner `pairCorner σ b x''` (coordinates `i = σ 0`, `j = σ 1` frozen at
`b i`, `b j`) over the orthant of the remaining coordinates, for a suitable coordinate permutation
`σ` with `σ 0 = i` and `σ 1 = j`. -/
theorem integral_Iic_partial2_covDensity (hS : S.PosDef) {i j : Fin (m + 2)} (hij : i ≠ j)
    (b : Fin (m + 2) → ℝ) :
    ∃ σ : Equiv.Perm (Fin (m + 2)), σ 0 = i ∧ σ 1 = j ∧
      ∫ x in Set.Iic b, (((S⁻¹ *ᵥ x) i) * ((S⁻¹ *ᵥ x) j) - S⁻¹ i j) * covDensity S x
        = ∫ x'' in Set.Iic (fun k : Fin m => b (σ k.succ.succ)),
            covDensity S (pairCorner σ b x'') :=
  exists_perm_integral_Iic_mixed_deriv i j hij b (covDensity S)
    (fun x => -((S⁻¹ *ᵥ x) i) * covDensity S x)
    (fun x => (((S⁻¹ *ᵥ x) i) * ((S⁻¹ *ᵥ x) j) - S⁻¹ i j) * covDensity S x)
    (integrable_partial2_covDensity hS i j).integrableOn
    (fun y t _ => hasDerivAt_covDensity_partial_update hS y i j t)
    (fun y => (integrable_partial2_covDensity_update hS y i j).integrableOn)
    (fun y => tendsto_partial_covDensity_update_atBot hS y i j)
    (fun y _ t _ => hasDerivAt_covDensity_update hS y i t)
    (fun y _ => (integrable_partial_covDensity_update hS y i i).integrableOn)
    (fun y _ => tendsto_covDensity_update_atBot hS y i)

/-- The boundary integral of `integral_Iic_partial2_covDensity` is nonnegative: it integrates
the positive function `covDensity S` along `pairCorner σ b`. -/
theorem integral_Iic_pairCorner_covDensity_nonneg (hS : S.PosDef)
    (b : Fin (m + 2) → ℝ) (σ : Equiv.Perm (Fin (m + 2))) :
    0 ≤ ∫ x'' in Set.Iic (fun k : Fin m => b (σ k.succ.succ)),
      covDensity S (pairCorner σ b x'') :=
  integral_nonneg fun x'' => (covDensity_pos hS (pairCorner σ b x'')).le

end Orthant

end LatticeProb
