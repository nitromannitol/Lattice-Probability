/-
# Li--Shao normal comparison: route item 3 from the raw orthant derivative

Continuing `LatticeProb/Prob/NormalComparisonFinalTwo.lean`.  The final bound
`normalComparison_bound_of_orthant_pieces` takes the pair-sum form of the derivative of the
orthant integral as the hypothesis `hderiv`.  This file supplies the finite-sum algebra that
turns the **raw** orthant derivative (the explicit double integral over the half-space, the
analytic step) into that pair-sum form, then re-assembles the final bound with the raw derivative
as the hypothesis in place of the pair sum.

  `d/dt ∫_{x ≤ b} covDensity S_t x dx
      = (1/2) ∑ᵢⱼ (S - v • 1)ᵢⱼ I_ij(S_t)  =  ∑ᵢ ∑_{j > i} Sᵢⱼ I_ij(S_t)`,

where `I_ij(M) = orthantPartial2 M b i j`.  The diagonal weights vanish and the integrand is
symmetric, so the full double sum is twice the pair sum; on the pairs `B i j = S i j`.  No
`External` is touched, no `Prop` is frozen, and nothing is claimed about `Rotor.External.LSS`.
-/
import LatticeProb.Prob.NormalComparisonFinalTwo

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal Matrix

namespace LatticeProb

/-- **Route item 3, pair-sum form, from the raw orthant derivative.**  Given the raw derivative of
the orthant integral along the smart path,
`(1/2) ∑ᵢⱼ (S - v • 1)ᵢⱼ I_ij(S_t₀)`, the vanishing diagonal and the symmetry of the
integrand rewrite it as the pair sum `∑ᵢ ∑_{j > i} Sᵢⱼ I_ij(S_t₀)`. -/
theorem hasDerivAt_orthant_covDensity_path_pairs_of_raw {n : ℕ} {v : ℝ} (hv : 0 < v)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) (hdiag : ∀ i, S i i = v)
    (b : Fin n → ℝ) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hraw : HasDerivAt (fun t => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath v S t) x)
      (1 / 2 * ∑ i, ∑ j, (S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) i j *
        orthantPartial2 (normalComparisonSmartPath v S t₀) b i j) t₀) :
    HasDerivAt (fun t => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath v S t) x)
      (∑ i, ∑ j ∈ Finset.Ioi i,
        S i j * orthantPartial2 (normalComparisonSmartPath v S t₀) b i j) t₀ := by
  refine hraw.congr_deriv ?_
  have hPD : (normalComparisonSmartPath v S t₀).PosDef :=
    normalComparisonSmartPath_posDef hS hv ⟨ht₀.1.le, ht₀.2⟩
  have hBii : ∀ i, (S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) i i = 0 := fun i => by
    simp [hdiag i]
  have hBij : ∀ i j, i ≠ j → (S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) i j = S i j :=
    fun i j h => by simp [Matrix.one_apply_ne h]
  have hBsymm : ∀ i j, (S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) i j
      = (S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) j i := fun i j => by
    have hSs : S i j = S j i := by simpa using hS.isHermitian.apply j i
    by_cases h : i = j
    · subst h; rfl
    · rw [hBij i j h, hBij j i (Ne.symm h), hSs]
  have hIsymm : ∀ i j, orthantPartial2 (normalComparisonSmartPath v S t₀) b i j
      = orthantPartial2 (normalComparisonSmartPath v S t₀) b j i :=
    fun i j => orthantPartial2_comm hPD b i j
  have key := sum_sum_eq_two_mul_sum_Ioi
    (fun i j => (S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) i j *
      orthantPartial2 (normalComparisonSmartPath v S t₀) b i j)
    (fun i j => by rw [hBsymm i j, hIsymm i j]) (fun i => by rw [hBii i, zero_mul])
  rw [key]
  have hrw : ∀ i, ∑ j ∈ Finset.Ioi i,
      (S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) i j *
        orthantPartial2 (normalComparisonSmartPath v S t₀) b i j
      = ∑ j ∈ Finset.Ioi i, S i j *
        orthantPartial2 (normalComparisonSmartPath v S t₀) b i j := by
    intro i
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hBij i j (ne_of_lt (Finset.mem_Ioi.mp hj))]
  simp only [hrw]
  ring

/-- **The route's final normal-comparison bound, from the raw orthant derivative.**  Same
conclusion as `normalComparison_bound_of_orthant_pieces`, but the analytic input is the raw
orthant derivative `hraw`; the pair-sum form is discharged by
`hasDerivAt_orthant_covDensity_path_pairs_of_raw`.  The remaining hypotheses `hlim`, `hcont`,
`hraw`, `hpartial` are the route's endpoint/continuity/derivative/density inputs. -/
theorem normalComparison_bound_of_orthant_raw {m : ℕ} {v : ℝ≥0} (hv : 0 < v)
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
  refine normalComparison_bound_of_orthant_pieces hv hS hdiag hnonneg b hlim hcont ?_ hpartial
  intro T hT t ht
  exact hasDerivAt_orthant_covDensity_path_pairs_of_raw (NNReal.coe_pos.mpr hv) hS hdiag b
    ⟨ht.1, ht.2.trans hT.2⟩ (hraw T hT t ht)

end LatticeProb
