/-
# Normal comparison (Li--Shao): the limit `t ↑ 1` and the final bound

Route item 8.  The interpolation on `[0, T]`, `T < 1`, is taken as a hypothesis
(`normalComparison_bound_of_interpolation`) and is discharged by `NormalComparisonInterpolation`.
Along the smart path `M t = (1 - t) • (v • 1) + t • S` write
`F t = ∫ x in Iic b, covDensity (M t) x`.  This file proves

* `F 0` is the product of the one-dimensional marginal masses (`integral_orthant_smartPath_zero`);
* `F t → P(Y ≤ b)` as `t ↑ 1`, for `S` positive semidefinite with constant diagonal
  (`tendsto_integral_orthant_smartPath`), although `N(0, S)` may be singular;
* the right-hand side of the interpolation is continuous at `T = 1`
  (`tendsto_normalComparison_remainder`);
* passing to the limit in `F 0 ≤ F T ≤ F 0 + R T` gives the normal comparison inequality with
  constant `1/4` (`normalComparison_bound_of_interpolation`).
-/
import Mathlib
import LatticeProb.Prob.NormalComparisonEndpoint
import LatticeProb.Prob.GaussCovDensityScalar
import LatticeProb.Prob.GaussCovDensityOrthantLink

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal Matrix

namespace LatticeProb

section Limit

variable {m : ℕ} {v : ℝ≥0} {S : Matrix (Fin m) (Fin m) ℝ}

/-- The orthant integral at the start of the smart path is the product of the marginal masses:
`∫_{Iic b} covDensity (v • 1) = ∏ i, N(0, v)((-∞, b i])`. -/
theorem integral_orthant_smartPath_zero (hv : 0 < v) (b : Fin m → ℝ) :
    (∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S 0) x) =
      ∏ i, (gaussianReal 0 v (Set.Iic (b i))).toReal := by
  rw [normalComparisonSmartPath_zero,
    ← multivariateGaussian_orthant_toReal_eq (posDef_scalar_one hv) b]
  exact multivariateGaussian_orthant_scalar hv b

/-- **Left-continuity of the orthant integral along the smart path at `t = 1`.**  For `S`
positive semidefinite with constant diagonal `v > 0`, the density integrals
`∫_{Iic b} covDensity (M t)` converge, as `t ↑ 1`, to the orthant probability of `N(0, S)`
(which need not have a density). -/
theorem tendsto_integral_orthant_smartPath (hv : 0 < v) (hS : S.PosSemidef)
    (hdiag : ∀ i, S i i = (v : ℝ)) (b : Fin m → ℝ) :
    Tendsto
      (fun t : ℝ => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S t) x)
      (𝓝[<] 1)
      (𝓝 (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S
        {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i}).toReal) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.mpr hv
  refine (tendsto_multivariateGaussian_orthant_path hv' hS hdiag b).congr' ?_
  refine eventuallyEq_of_mem (Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)) ?_
  intro t ht
  exact multivariateGaussian_orthant_toReal_eq
    (normalComparisonSmartPath_posDef hS hv' ⟨ht.1.le, ht.2⟩) b

/-- **The right-hand side of the interpolation is continuous at `T = 1`.**  For nonnegative
correlations the denominator `2 v (1 + T (S i j / v))` is positive near `T = 1`, so the double
sum of `S i j * ((4 v)⁻¹ * exp (-(b i² + b j²) / (2 v (1 + T (S i j / v)))))` converges, as
`T ↑ 1`, to its value at `T = 1`. -/
theorem tendsto_normalComparison_remainder (hv : 0 < v) (hnonneg : ∀ i j, 0 ≤ S i j)
    (b : Fin m → ℝ) :
    Tendsto (fun T : ℝ => ∑ i, ∑ j ∈ Finset.Ioi i, S i j * ((4 * (v : ℝ))⁻¹ *
        Real.exp (-(b i ^ 2 + b j ^ 2) / (2 * (v : ℝ) * (1 + T * (S i j / (v : ℝ)))))))
      (𝓝[<] 1)
      (𝓝 (∑ i, ∑ j ∈ Finset.Ioi i, S i j * ((4 * (v : ℝ))⁻¹ *
        Real.exp (-(b i ^ 2 + b j ^ 2) / (2 * (v : ℝ) * (1 + 1 * (S i j / (v : ℝ)))))))) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.mpr hv
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
  have hr : 0 ≤ S i j / (v : ℝ) := div_nonneg (hnonneg i j) hv'.le
  have hden : 2 * (v : ℝ) * (1 + (1 : ℝ) * (S i j / (v : ℝ))) ≠ 0 := by
    have : 0 < 2 * (v : ℝ) * (1 + (1 : ℝ) * (S i j / (v : ℝ))) := by positivity
    exact this.ne'
  have hcont : ContinuousAt (fun T : ℝ => S i j * ((4 * (v : ℝ))⁻¹ *
      Real.exp (-(b i ^ 2 + b j ^ 2) / (2 * (v : ℝ) * (1 + T * (S i j / (v : ℝ))))))) 1 := by
    refine continuousAt_const.mul (continuousAt_const.mul (Real.continuous_exp.continuousAt.comp
      (continuousAt_const.div ?_ hden)))
    fun_prop
  exact hcont.tendsto.mono_left nhdsWithin_le_nhds

end Limit

/-- The limit step.  The hypothesis `hinterp` is the interpolation on `[0, T]`, `T < 1`
(proved separately in `NormalComparisonInterpolation`); the conclusion is the normal comparison
inequality with constant `1/4`. -/
theorem normalComparison_bound_of_interpolation {m : ℕ} {v : ℝ≥0} (hv : 0 < v)
    {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosSemidef) (hdiag : ∀ i, S i i = (v : ℝ))
    (hnonneg : ∀ i j, 0 ≤ S i j) (b : Fin m → ℝ)
    (hinterp : ∀ T ∈ Set.Ico (0 : ℝ) 1,
      (∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S 0) x)
          ≤ ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S T) x ∧
        (∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S T) x)
          - (∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S 0) x)
        ≤ ∑ i, ∑ j ∈ Finset.Ioi i, S i j *
            ((4 * (v : ℝ))⁻¹ * Real.exp (-(b i ^ 2 + b j ^ 2) /
              (2 * (v : ℝ) * (1 + T * (S i j / (v : ℝ))))))) :
    |(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S
          {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i}).toReal -
        ∏ i, (gaussianReal 0 v (Set.Iic (b i))).toReal| ≤
      (1 / 4) * ∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
        S i j / (v : ℝ) *
          Real.exp (-(b i ^ 2 + b j ^ 2) / (2 * (v : ℝ) * (1 + S i j / (v : ℝ)))) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.mpr hv
  have hF0 := integral_orthant_smartPath_zero (S := S) hv b
  have hlim := tendsto_integral_orthant_smartPath hv hS hdiag b
  have hR := tendsto_normalComparison_remainder hv hnonneg b
  have hev : ∀ᶠ T in 𝓝[<] (1 : ℝ), T ∈ Set.Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)
  have h1 := ge_of_tendsto hlim (hev.mono fun T hT => (hinterp T ⟨hT.1.le, hT.2⟩).1)
  have h2 := le_of_tendsto_of_tendsto hlim
    ((tendsto_const_nhds (x := ∫ x in Set.Iic b,
      covDensity (normalComparisonSmartPath (v : ℝ) S 0) x)).add hR)
    (hev.mono fun T hT => by
      have := (hinterp T ⟨hT.1.le, hT.2⟩).2
      simp only
      linarith)
  rw [hF0] at h1 h2
  rw [abs_of_nonneg (sub_nonneg.mpr h1)]
  have hrw : (∑ i, ∑ j ∈ Finset.Ioi i, S i j * ((4 * (v : ℝ))⁻¹ *
        Real.exp (-(b i ^ 2 + b j ^ 2) / (2 * (v : ℝ) * (1 + 1 * (S i j / (v : ℝ))))))) =
      (1 / 4) * ∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
        S i j / (v : ℝ) *
          Real.exp (-(b i ^ 2 + b j ^ 2) / (2 * (v : ℝ) * (1 + S i j / (v : ℝ)))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_mul]
    field_simp
  rw [← hrw]
  linarith

end LatticeProb
