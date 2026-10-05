/-
# Normal comparison (Li--Shao): the final bound assembly

Route item 8.  Along the smart path `M t = (1 - t) • (v • 1) + t • S` write
`F t = ∫ x in Iic b, covDensity (M t) x`.  This file assembles the final bound from the
interpolation and the two endpoint facts, both of which are the remaining route steps:

* the interpolation on `[0, T]`, `T < 1` (the boundary-integral, covariance-differentiation and
  scale steps assembled), taken as the hypothesis `hinterp`;
* the starting value `F 0 = ∏ i, N(0, v)(Iic (b i))`, taken as `hF0`;
* the left-continuity `F t → P(N(0,S) ≤ b)` as `t ↑ 1`, taken as `hlim`.

The right-hand side's continuity at `T = 1` is proved here (`tendsto_normalComparison_remainder`),
and passing to the limit in `F 0 ≤ F T ≤ F 0 + R T` gives the normal comparison inequality with
constant `1/4`.  No `External` is touched and no `Prop` is frozen.
-/
import LatticeProb.Prob.NormalComparison
import LatticeProb.Prob.NormalComparisonCovariance

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal Matrix

namespace LatticeProb

variable {m : ℕ} {v : ℝ≥0} {S : Matrix (Fin m) (Fin m) ℝ}

section Limit

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

/-- **The final bound from the interpolation and the endpoint facts.**  The hypothesis
`hinterp` is the interpolation on `[0, T]`, `T < 1` (proved separately by assembling the
boundary-integral, covariance-differentiation and scale steps); `hF0` is the starting value at
the product law and `hlim` the left-continuity at the endpoint.  The conclusion is the normal
comparison inequality with constant `1/4`. -/
theorem normalComparison_bound_of_interpolation (hv : 0 < v)
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
