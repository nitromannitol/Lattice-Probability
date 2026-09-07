/-
The orthant bound for a Gaussian with nearly isotropic covariance.

A centred Gaussian on `ℝ^m` whose covariance has quadratic form between `1-δ`
and `1+δ` is the image of the standard Gaussian under a linear map `A` with
`(1-δ)|x|² ≤ |Ax|² ≤ (1+δ)|x|²`.  Its density is then at most
`((1+δ)/(1-δ))^{m/2}` times the density of the isotropic Gaussian of variance
`1+δ`, and integrating that comparison over an orthant gives the persistence
bound `P(G_j ≤ η for all j) ≤ [√((1+δ)/(1-δ)) Φ(η/√(1+δ))]^m`.
-/
import Mathlib
import LatticeProb.Prob.GaussDensity

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal NNReal

/-! ### The product of one-dimensional Gaussian densities -/

theorem prod_gaussianPDFReal {ι : Type*} [Fintype ι] (v : ℝ≥0) (x : ι → ℝ) :
    ∏ i, gaussianPDFReal 0 v (x i)
      = (√(2 * π * v))⁻¹ ^ (Fintype.card ι) * rexp (-(∑ i, (x i) ^ 2) / (2 * v)) := by
  simp only [gaussianPDFReal, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum, Finset.card_univ]
  congr 1
  rw [← Finset.sum_div, ← Finset.sum_neg_distrib]

theorem prod_gaussianPDF {ι : Type*} [Fintype ι] (v : ℝ≥0) (x : ι → ℝ) :
    ∏ i, gaussianPDF 0 v (x i)
      = ENNReal.ofReal ((√(2 * π * v))⁻¹ ^ (Fintype.card ι)
          * rexp (-(∑ i, (x i) ^ 2) / (2 * v))) := by
  rw [← prod_gaussianPDFReal v x, gaussianPDF_def,
    ← ENNReal.ofReal_prod_of_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _]

/-! ### Linear change of variables for a density -/

/-- **Linear change of variables.**  Pushing a density forward along a linear
equivalence divides it by the absolute determinant. -/
theorem map_withDensity_linearEquiv_apply {ι : Type*} [Fintype ι]
    (A : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι)
    {g : EuclideanSpace ℝ ι → ℝ≥0∞} (hg : Measurable g)
    {T : Set (EuclideanSpace ℝ ι)} (hT : MeasurableSet T) :
    (((volume : Measure (EuclideanSpace ℝ ι)).withDensity g).map A) T
      = ENNReal.ofReal |(LinearMap.det (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι))⁻¹|
          * ∫⁻ y in T, g (A.symm y) ∂volume := by
  have hAmeas : Measurable (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) := by
    have : Continuous (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) :=
      LinearMap.continuous_of_finiteDimensional (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
    exact this.measurable
  have hAsymm : Measurable (A.symm : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) := by
    have : Continuous (A.symm : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) :=
      LinearMap.continuous_of_finiteDimensional
        (A.symm : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
    exact this.measurable
  have hdet : LinearMap.det (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) ≠ 0 :=
    (LinearEquiv.isUnit_det' A).ne_zero
  have hF : Measurable (T.indicator fun y => g (A.symm y)) := (hg.comp hAsymm).indicator hT
  have hpt : ∀ x : EuclideanSpace ℝ ι,
      (T.indicator fun y => g (A.symm y)) (A x) = ((A : EuclideanSpace ℝ ι → _) ⁻¹' T).indicator g x := by
    intro x
    by_cases hx : A x ∈ T
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ (A : _ → _) ⁻¹' T from hx)]
      simp
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ (A : _ → _) ⁻¹' T from hx)]
  rw [Measure.map_apply hAmeas hT, withDensity_apply _ (hAmeas hT),
    ← lintegral_indicator (hAmeas hT), ← lintegral_indicator hT]
  have hmapvol : Measure.map (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
      (volume : Measure (EuclideanSpace ℝ ι))
      = ENNReal.ofReal |(LinearMap.det (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι))⁻¹|
          • (volume : Measure (EuclideanSpace ℝ ι)) :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet
  rw [lintegral_congr fun x => (hpt x).symm, ← lintegral_map hF hAmeas, hmapvol,
    lintegral_smul_measure, smul_eq_mul]

/-! ### The density comparison -/

theorem euclidean_sum_sq (ι : Type*) [Fintype ι] (y : EuclideanSpace ℝ ι) :
    ∑ i, (y i) ^ 2 = ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact (Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]).symm

/-- **Density domination.**  If the pushforward density of the standard Gaussian
is bounded by `c` times the isotropic density of variance `v`, so is the
measure. -/
theorem map_stdGaussian_le_smul {ι : Type*} [Fintype ι]
    (A : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) (c : ℝ≥0∞) (v : ℝ≥0)
    (hdens : ∀ y : EuclideanSpace ℝ ι,
      ENNReal.ofReal |(LinearMap.det (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι))⁻¹|
          * (∏ i, gaussianPDF 0 1 ((A.symm y) i))
        ≤ c * ∏ i, gaussianPDF 0 v (y i)) :
    (stdGaussian (EuclideanSpace ℝ ι)).map A
      ≤ c • (volume : Measure (EuclideanSpace ℝ ι)).withDensity
          (fun y => ∏ i, gaussianPDF 0 v (y i)) := by
  have hmeas1 : Measurable fun y : EuclideanSpace ℝ ι => ∏ i, gaussianPDF 0 1 (y i) :=
    Finset.measurable_prod _ fun i _ => (measurable_gaussianPDF 0 1).comp (by fun_prop)
  have hmeas2 : Measurable fun y : EuclideanSpace ℝ ι => ∏ i, gaussianPDF 0 v (y i) :=
    Finset.measurable_prod _ fun i _ => (measurable_gaussianPDF 0 v).comp (by fun_prop)
  have hAsymm : Measurable (A.symm : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) := by
    have : Continuous (A.symm : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) :=
      LinearMap.continuous_of_finiteDimensional
        (A.symm : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
    exact this.measurable
  rw [stdGaussian_euclidean_eq_withDensity]
  refine Measure.le_iff.mpr fun T hT => ?_
  have hmeas1' : Measurable fun y : EuclideanSpace ℝ ι => ∏ i, gaussianPDF 0 1 ((A.symm y) i) :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDF 0 1).comp ((measurable_pi_apply i).comp (by fun_prop))
  rw [map_withDensity_linearEquiv_apply A hmeas1 hT, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ hT]
  calc ENNReal.ofReal |(LinearMap.det (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι))⁻¹|
        * ∫⁻ y in T, (∏ i, gaussianPDF 0 1 ((A.symm y) i)) ∂volume
      = ∫⁻ y in T, ENNReal.ofReal
          |(LinearMap.det (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι))⁻¹|
            * (∏ i, gaussianPDF 0 1 ((A.symm y) i)) ∂volume :=
        (lintegral_const_mul _ hmeas1').symm
    _ ≤ ∫⁻ y in T, c * (∏ i, gaussianPDF 0 v (y i)) ∂volume :=
        lintegral_mono fun y => hdens y
    _ = c * ∫⁻ y in T, (∏ i, gaussianPDF 0 v (y i)) ∂volume := lintegral_const_mul _ hmeas2

end LatticeProb

end
