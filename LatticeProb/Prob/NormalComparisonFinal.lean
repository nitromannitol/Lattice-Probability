/-
Normal comparison: the final bound from supplied endpoint facts.

The remainder-limit theorem is imported from NormalComparisonLimit.
The retained endpoint form assumes hF0, hlim and hinterp and concludes
the normal-comparison bound with constant 1/4.
-/
import LatticeProb.Prob.NormalComparison
import LatticeProb.Prob.NormalComparisonCovariance
import LatticeProb.Prob.NormalComparisonLimit
import LatticeProb.Prob.NormalComparisonExists

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal Matrix

namespace LatticeProb

variable {m : ℕ} {v : ℝ≥0} {S : Matrix (Fin m) (Fin m) ℝ}

/-- **The final bound from the interpolation and the endpoint facts.**  The hypothesis
`hinterp` is the interpolation on `[0, T]`, `T < 1` (proved separately by assembling the
boundary-integral, covariance-differentiation and scale steps); `hF0` is the starting value at
the product law and `hlim` the left-continuity at the endpoint.  The conclusion is the normal
comparison inequality with constant `1/4`. -/
theorem normalComparison_bound_of_interpolation_of_endpoints (hv : 0 < v)
    (hnonneg : ∀ i j, 0 ≤ S i j) (b : Fin m → ℝ)
    (hF0 : (∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S 0) x) =
      ∏ i, (gaussianReal 0 v (Set.Iic (b i))).toReal)
    (hlim : Tendsto
      (fun t : ℝ => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S t) x)
      (𝓝[<] 1)
      (𝓝 (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S
        {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i}).toReal))
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
  have hR := tendsto_normalComparison_remainder (S := S) hv hnonneg b
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
