/-
# Li--Shao normal comparison: the density along the smart path (route item 3, pointwise)

Continuing the route after `LatticeProb/Prob/NormalComparisonFinalSix.lean`.  The raw orthant
derivative `hasDerivAt_orthant_covDensity_path` differentiates the integrand
`covDensity (normalComparisonSmartPath v S t) x` in `t`.  This file supplies that pointwise density
derivative: writing the smart path as the affine line `S_t = v • 1 + t • (S - v • 1)`, the
density
derivative is

  `d/dt covDensity S_t x = (1/2) ∑ᵢⱼ (S - v • 1)ᵢⱼ
      ((S_t⁻¹ x)ᵢ (S_t⁻¹ x)ⱼ - S_t⁻¹ᵢⱼ) covDensity S_t x`,

reducing it to the matrix-direction derivative `hasDerivAt_covDensity_add_smul`, taken as the
analytic input.

No `External` is touched, no `Prop` is frozen, and nothing is claimed about `Rotor.External.LSS`.
-/
import LatticeProb.Prob.NormalComparisonBoundary
import LatticeProb.Prob.NormalComparisonCovariance

open MeasureTheory Matrix

namespace LatticeProb

/-- The smart path as an affine line of matrices: `S_t = v • 1 + t • (S - v • 1)`. -/
theorem normalComparisonSmartPath_eq_add_smul {n : ℕ} (v : ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) :
    normalComparisonSmartPath v S t =
      v • (1 : Matrix (Fin n) (Fin n) ℝ)
        + t • (S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  ext i j
  simp only [normalComparisonSmartPath, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    smul_eq_mul]
  ring

/-- **Route item 3, pointwise density derivative, from the matrix-direction derivative.**  Given
`hasDerivAt_covDensity_add_smul` (the derivative of `covDensity (A + t • B) x` in `t`), the
density
along the smart path has derivative
`(1/2) ∑ᵢⱼ (S - v • 1)ᵢⱼ ((S_t⁻¹ x)ᵢ (S_t⁻¹ x)ⱼ - S_t⁻¹ᵢⱼ) covDensity S_t x` for
`t ∈ [0, 1)`. -/
theorem hasDerivAt_covDensity_smartPath_of_add_smul {n : ℕ} {v : ℝ} (hv : 0 < v)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (hadd : ∀ (A B : Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ), (A + t₀ • B).PosDef →
      ∀ x : Fin n → ℝ,
      HasDerivAt (fun s : ℝ => covDensity (A + s • B) x)
        (1 / 2 * ∑ i, ∑ j, B i j *
          ((((A + t₀ • B)⁻¹ *ᵥ x) i * ((A + t₀ • B)⁻¹ *ᵥ x) j
              - (A + t₀ • B)⁻¹ i j)
            * covDensity (A + t₀ • B) x)) t₀)
    (x : Fin n → ℝ) :
    HasDerivAt (fun s : ℝ => covDensity (normalComparisonSmartPath v S s) x)
      (1 / 2 * ∑ i, ∑ j, (S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) i j *
        ((((normalComparisonSmartPath v S t)⁻¹ *ᵥ x) i
            * ((normalComparisonSmartPath v S t)⁻¹ *ᵥ x) j
            - (normalComparisonSmartPath v S t)⁻¹ i j)
          * covDensity (normalComparisonSmartPath v S t) x)) t := by
  have hPD : (v • (1 : Matrix (Fin n) (Fin n) ℝ) + t • (S - v • 1)).PosDef := by
    rw [← normalComparisonSmartPath_eq_add_smul]
    exact normalComparisonSmartPath_posDef hS hv ht
  have h := hadd (v • (1 : Matrix (Fin n) (Fin n) ℝ))
    (S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) t hPD x
  simpa only [← normalComparisonSmartPath_eq_add_smul] using h

end LatticeProb
