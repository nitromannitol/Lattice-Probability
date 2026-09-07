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

open MeasureTheory ProbabilityTheory Real Matrix

open scoped ENNReal NNReal MatrixOrder

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

/-- **A norm-expanding linear equivalence has a large determinant.** -/
theorem le_abs_det_of_norm_le {ι : Type*} [Fintype ι]
    (A : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) {c : ℝ} (hc : 0 < c)
    (h : ∀ x : EuclideanSpace ℝ ι, c * ‖x‖ ≤ ‖A x‖) :
    c ^ (Fintype.card ι)
      ≤ |LinearMap.det (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)| := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hcard : Fintype.card ι = 0 := by simp
    have hrank : Module.finrank ℝ (EuclideanSpace ℝ ι) = 0 := by
      rw [finrank_euclideanSpace, hcard]
    have hdet1 : LinearMap.det (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) = 1 :=
      LinearMap.det_eq_one_of_finrank_eq_zero hrank _
    rw [hcard, hdet1]
    simp
  · have hsub : Metric.ball (0 : EuclideanSpace ℝ ι) c
        ⊆ (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) '' Metric.ball (0 : EuclideanSpace ℝ ι) 1 := by
      intro y hy
      refine ⟨A.symm y, ?_, by simp⟩
      have h1 : c * ‖A.symm y‖ ≤ ‖y‖ := by
        have := h (A.symm y)
        simpa using this
      have h2 : ‖y‖ < c := by simpa [Metric.mem_ball, dist_zero_right] using hy
      have : ‖A.symm y‖ < 1 := by nlinarith [norm_nonneg (A.symm y)]
      simpa [Metric.mem_ball, dist_zero_right] using this
    have hVpos : (0 : ℝ≥0∞) < volume (Metric.ball (0 : EuclideanSpace ℝ ι) 1) :=
      Metric.measure_ball_pos volume 0 one_pos
    have hVtop : volume (Metric.ball (0 : EuclideanSpace ℝ ι) 1) ≠ ⊤ := measure_ball_lt_top.ne
    have hmono : volume (Metric.ball (0 : EuclideanSpace ℝ ι) c)
        ≤ volume ((A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) ''
            Metric.ball (0 : EuclideanSpace ℝ ι) 1) := measure_mono hsub
    rw [Measure.addHaar_ball volume 0 hc.le,
      show ((A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) '' Metric.ball (0 : EuclideanSpace ℝ ι) 1)
        = (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) ''
            Metric.ball (0 : EuclideanSpace ℝ ι) 1 from rfl,
      Measure.addHaar_image_linearMap, finrank_euclideanSpace] at hmono
    have hfin : ENNReal.ofReal
        |LinearMap.det (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)|
        * volume (Metric.ball (0 : EuclideanSpace ℝ ι) 1) ≠ ⊤ := by finiteness
    have htoReal := ENNReal.toReal_mono hfin hmono
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ c ^ Fintype.card ι),
      ENNReal.toReal_ofReal (abs_nonneg _)] at htoReal
    have hVR : (0 : ℝ) < (volume (Metric.ball (0 : EuclideanSpace ℝ ι) 1)).toReal :=
      ENNReal.toReal_pos hVpos.ne' hVtop
    exact le_of_mul_le_mul_right htoReal hVR

/-- **The orthant bound for a Gaussian with nearly isotropic covariance.**  If
`A` expands norms by between `√(1-δ)` and `√(1+δ)`, the image of the standard
Gaussian under `A` gives an orthant at most
`[√((1+δ)/(1-δ)) Φ(η/√(1+δ))]^m`. -/
theorem orthant_map_stdGaussian_le {ι : Type*} [Fintype ι]
    (A : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hlo : ∀ x : EuclideanSpace ℝ ι, (1 - δ) * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2)
    (hhi : ∀ x : EuclideanSpace ℝ ι, ‖A x‖ ^ 2 ≤ (1 + δ) * ‖x‖ ^ 2) (η : ℝ) :
    ((stdGaussian (EuclideanSpace ℝ ι)).map A) {y : EuclideanSpace ℝ ι | ∀ i, y i ≤ η}
      ≤ (ENNReal.ofReal (√((1 + δ) / (1 - δ)))
          * gaussianReal 0 1 (Set.Iic (η / √(1 + δ)))) ^ (Fintype.card ι) := by
  set m := Fintype.card ι with hm
  have h1d : (0 : ℝ) < 1 - δ := by linarith
  have h1u : (0 : ℝ) < 1 + δ := by linarith
  have hs1d : (0 : ℝ) < √(1 - δ) := Real.sqrt_pos.mpr h1d
  have hs1u : (0 : ℝ) < √(1 + δ) := Real.sqrt_pos.mpr h1u
  have hspi : (0 : ℝ) < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
  set v : ℝ≥0 := ⟨1 + δ, h1u.le⟩ with hvdef
  have hvc : ((v : ℝ≥0) : ℝ) = 1 + δ := rfl
  have hvne : v ≠ 0 := fun hcon => by
    have : ((v : ℝ≥0) : ℝ) = 0 := by rw [hcon]; simp
    rw [hvc] at this; linarith
  -- the determinant is at least `(1-δ)^{m/2}`
  have hnormlo : ∀ x : EuclideanSpace ℝ ι, √(1 - δ) * ‖x‖ ≤ ‖A x‖ := by
    intro x
    have hsq : (√(1 - δ) * ‖x‖) ^ 2 = (1 - δ) * ‖x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt h1d.le]
    nlinarith [hlo x, norm_nonneg (A x), norm_nonneg x, hs1d]
  have hdet : (√(1 - δ)) ^ m
      ≤ |LinearMap.det (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)| :=
    le_abs_det_of_norm_le A hs1d hnormlo
  have hdetpos : (0 : ℝ) < |LinearMap.det (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)| :=
    lt_of_lt_of_le (by positivity) hdet
  -- the density comparison
  have hdens : ∀ y : EuclideanSpace ℝ ι,
      ENNReal.ofReal |(LinearMap.det (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι))⁻¹|
          * (∏ i, gaussianPDF 0 1 ((A.symm y) i))
        ≤ (ENNReal.ofReal (√((1 + δ) / (1 - δ)))) ^ m * ∏ i, gaussianPDF 0 v (y i) := by
    intro y
    have hAy : A (A.symm y) = y := by simp
    have hy2 : ‖y‖ ^ 2 ≤ (1 + δ) * ‖A.symm y‖ ^ 2 := by
      have := hhi (A.symm y)
      rwa [hAy] at this
    rw [prod_gaussianPDF, prod_gaussianPDF, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [euclidean_sum_sq, euclidean_sum_sq, hvc]
    have hexp : rexp (-‖A.symm y‖ ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))
        ≤ rexp (-‖y‖ ^ 2 / (2 * (1 + δ))) := by
      refine Real.exp_le_exp.mpr ?_
      have h2 : (0 : ℝ) < 2 * (1 + δ) := by positivity
      have hstep : ‖y‖ ^ 2 / (2 * (1 + δ)) ≤ ‖A.symm y‖ ^ 2 / 2 := by
        rw [← sub_nonneg,
          show ‖A.symm y‖ ^ 2 / 2 - ‖y‖ ^ 2 / (2 * (1 + δ))
            = ((1 + δ) * ‖A.symm y‖ ^ 2 - ‖y‖ ^ 2) / (2 * (1 + δ)) by field_simp]
        exact div_nonneg (by linarith [hy2]) h2.le
      rw [NNReal.coe_one, mul_one, neg_div, neg_div, neg_le_neg_iff]
      exact hstep
    have hconst : |(LinearMap.det (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι))⁻¹|
          * (√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹ ^ m
        ≤ (√((1 + δ) / (1 - δ))) ^ m * (√(2 * π * (1 + δ)))⁻¹ ^ m := by
      have hkey : √((1 + δ) / (1 - δ)) * (√(2 * π * (1 + δ)))⁻¹
          = (√(1 - δ))⁻¹ * (√(2 * π))⁻¹ := by
        rw [Real.sqrt_div h1u.le, Real.sqrt_mul (by positivity)]
        field_simp
      rw [← mul_pow, hkey, mul_pow, NNReal.coe_one, mul_one, abs_inv]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [inv_pow]
      exact inv_anti₀ (by positivity) hdet
    have hnn1 : (0 : ℝ) ≤ rexp (-‖A.symm y‖ ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) := (Real.exp_pos _).le
    have hnn2 : (0 : ℝ) ≤ |(LinearMap.det (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι))⁻¹|
        * (√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹ ^ m := by positivity
    calc |(LinearMap.det (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι))⁻¹|
          * ((√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹ ^ m
            * rexp (-‖A.symm y‖ ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))))
        = (|(LinearMap.det (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι))⁻¹|
            * (√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹ ^ m)
          * rexp (-‖A.symm y‖ ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) := by ring
      _ ≤ ((√((1 + δ) / (1 - δ))) ^ m * (√(2 * π * (1 + δ)))⁻¹ ^ m)
            * rexp (-‖y‖ ^ 2 / (2 * (1 + δ))) := by
          exact mul_le_mul hconst hexp hnn1 (by positivity)
      _ = (√((1 + δ) / (1 - δ))) ^ m
            * ((√(2 * π * (1 + δ)))⁻¹ ^ m * rexp (-‖y‖ ^ 2 / (2 * (1 + δ)))) := by ring
  -- combine
  have hle := map_stdGaussian_le_smul A ((ENNReal.ofReal (√((1 + δ) / (1 - δ)))) ^ m) v hdens
  have := orthant_le_of_le_smul (μ := (stdGaussian (EuclideanSpace ℝ ι)).map A)
    ((ENNReal.ofReal (√((1 + δ) / (1 - δ)))) ^ m) v hvne hle η
  rw [gaussianReal_Iic_eq v hvne η, hvc, ← mul_pow] at this
  exact this

/-! ### The multivariate Gaussian -/

open scoped RealInnerProductSpace in
/-- The quadratic form of the covariance is the squared norm of the image under
its square root. -/
theorem norm_sq_toEuclideanCLM_sqrt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (x : EuclideanSpace ℝ ι) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x‖ ^ 2 = x ⬝ᵥ S *ᵥ x := by
  have hsa : IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) :=
    (CFC.sqrt_nonneg S).isSelfAdjoint.map _
  rw [← real_inner_self_eq_norm_sq, ← ContinuousLinearMap.adjoint_inner_right, hsa.adjoint_eq,
    ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
    CFC.sqrt_mul_sqrt_self _ hS.nonneg, inner_toEuclideanCLM]

/-- **The orthant bound for the multivariate Gaussian.**  If the quadratic form
of the covariance lies between `1-δ` and `1+δ`, the probability that all
coordinates are at most `η` is at most `[√((1+δ)/(1-δ)) Φ(η/√(1+δ))]^m`.

The hypothesis that `S` is positive semidefinite cannot be dropped: for a matrix
whose quadratic form is positive but which is not Hermitian, `CFC.sqrt S = 0`
and `multivariateGaussian 0 S` is the Dirac mass at the origin, whose orthant
probability is `1` for `η ≥ 0`. -/
theorem multivariateGaussian_orthant_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hlo : ∀ v : EuclideanSpace ℝ ι, (1 - δ) * ‖v‖ ^ 2 ≤ v ⬝ᵥ S *ᵥ v)
    (hhi : ∀ v : EuclideanSpace ℝ ι, v ⬝ᵥ S *ᵥ v ≤ (1 + δ) * ‖v‖ ^ 2) (η : ℝ) :
    multivariateGaussian 0 S {y : EuclideanSpace ℝ ι | ∀ i, y i ≤ η}
      ≤ (ENNReal.ofReal (√((1 + δ) / (1 - δ)))
          * gaussianReal 0 1 (Set.Iic (η / √(1 + δ)))) ^ (Fintype.card ι) := by
  have h1d : (0 : ℝ) < 1 - δ := by linarith
  have hnorm : ∀ x : EuclideanSpace ℝ ι,
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x‖ ^ 2 = x ⬝ᵥ S *ᵥ x :=
    norm_sq_toEuclideanCLM_sqrt hS
  have hinj : Function.Injective
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) := by
    intro x y hxy
    have h0 : Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hq := hlo (x - y)
    rw [← hnorm (x - y), h0] at hq
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hq
    have hz1 : ‖x - y‖ ≤ 0 := by
      by_contra hcon
      push Not at hcon
      have hpos : 0 < (1 - δ) * ‖x - y‖ ^ 2 := mul_pos h1d (pow_pos hcon 2)
      linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz1 (norm_nonneg _)))
  have hsurj : Function.Surjective
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) :
        EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) :=
    LinearMap.injective_iff_surjective.mp hinj
  set A : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι :=
    LinearEquiv.ofBijective
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) :
          EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
        EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) ⟨hinj, hsurj⟩ with hAdef
  have hAapp : ∀ x : EuclideanSpace ℝ ι,
      A x = Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x := fun x => rfl
  have hfun : (fun x : EuclideanSpace ℝ ι => (0 : EuclideanSpace ℝ ι)
      + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x) = ⇑A := by
    funext x
    rw [zero_add, hAapp]
  rw [multivariateGaussian, hfun]
  refine orthant_map_stdGaussian_le A hδ0 hδ1 (fun x => ?_) (fun x => ?_) η
  · rw [hAapp, hnorm]
    exact hlo x
  · rw [hAapp, hnorm]
    exact hhi x

end LatticeProb

end
