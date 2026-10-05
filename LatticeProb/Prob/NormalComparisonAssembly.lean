/-
# Normal comparison: the density/scale endpoint and the final bound assembly

Li--Shao normal comparison, route item 8.  The final bound
`normalComparison_bound_of_interpolation` takes three route facts as hypotheses: the starting
value `F 0 = ∏ i, N(0, v)(Iic (b i))` (the density/scale step at `t = 0`), the left-continuity of
the orthant integral at `t = 1`, and the interpolation on `[0, T]`, `T < 1`.

This file discharges the density/scale step.  It

* transports the orthant integral from `EuclideanSpace ℝ (Fin n)` to `Set.Iic b ⊆ Fin n → ℝ`
  (`lintegral_orthant_eq`);
* links the law `N(0, S)` to the integral of `covDensity S` (`multivariateGaussian_orthant_toReal_eq`);
* identifies the scalar matrix `v • 1` density as the product of the one-dimensional Gaussian
  densities (`covDensity_scalar`) and its orthant mass as the product of the marginal masses
  (`multivariateGaussian_orthant_scalar`);
* proves `integral_orthant_smartPath_zero`, the starting value of the smart path;
* assembles the final bound with only the remaining two route facts (the endpoint continuity and
  the interpolation) as hypotheses.

No `External` is touched and no `Prop` is frozen.
-/
import LatticeProb.Prob.NormalComparisonFinal
import LatticeProb.Prob.NormalComparisonCovariance

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal Matrix

namespace LatticeProb

/-! ### Orthant transport to `EuclideanSpace` -/

/-- **Orthant transport to `EuclideanSpace`.**  Pushing the orthant integral along the
volume-preserving `WithLp.toLp 2` turns it into an integral over `Set.Iic b`. -/
theorem lintegral_orthant_eq {n : ℕ} (b : Fin n → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i}, f y
      = ∫⁻ x in Set.Iic b, f (WithLp.toLp 2 x) := by
  have hmp : MeasurePreserving (⇑(MeasurableEquiv.toLp 2 (Fin n → ℝ)))
      (volume : Measure (Fin n → ℝ)) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    PiLp.volume_preserving_toLp (Fin n)
  have hS : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i} := by
    rw [show {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i}
        = ⋂ i, {y : EuclideanSpace ℝ (Fin n) | y i ≤ b i} by
      ext y; simp]
    exact MeasurableSet.iInter fun i =>
      measurableSet_le (by fun_prop : Measurable fun y : EuclideanSpace ℝ (Fin n) => y i)
        measurable_const
  have hpre : (MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹'
      {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i} = Set.Iic b := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Iic, Pi.le_def,
      MeasurableEquiv.coe_toLp]
  have hcongr : ∀ x : Fin n → ℝ,
      ({y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i}).indicator f
          ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) x)
        = ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹'
            {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i}).indicator
            (fun x => f ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) x)) x := by
    intro x
    by_cases hx : (MeasurableEquiv.toLp 2 (Fin n → ℝ)) x ∈
        {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i}
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem
        (show x ∈ (MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹'
          {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i} from hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem
        (show x ∉ (MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹'
          {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i} from hx)]
  rw [← lintegral_indicator hS, ← hmp.lintegral_comp (hf.indicator hS)]
  have h1 : (∫⁻ x : Fin n → ℝ,
        ({y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i}).indicator f
          ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) x))
      = ∫⁻ x in (MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹'
          {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i},
          f ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) x) := by
    rw [lintegral_congr fun x => hcongr x,
      lintegral_indicator (hS.preimage (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable)]
  rw [h1, hpre]
  rfl

/-! ### The orthant mass as a density integral -/

variable {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}

/-- The density `covDensity S` is continuous. -/
private lemma continuous_covDensity_link (S : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (covDensity S) := by
  unfold covDensity
  have h : Continuous fun x : Fin n → ℝ => x ⬝ᵥ (S⁻¹ *ᵥ x) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  fun_prop

/-- The orthant `{y | ∀ i, y i ≤ b i}` of `EuclideanSpace ℝ (Fin n)` is measurable. -/
private lemma measurableSet_orthant_link (b : Fin n → ℝ) :
    MeasurableSet {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i} := by
  rw [show {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i}
      = ⋂ i, {y : EuclideanSpace ℝ (Fin n) | y i ≤ b i} by
    ext y; simp]
  exact MeasurableSet.iInter fun i =>
    measurableSet_le (by fun_prop : Measurable fun y : EuclideanSpace ℝ (Fin n) => y i)
      measurable_const

/-- **The orthant mass of `N(0, S)` as a lower integral of the density.** -/
theorem multivariateGaussian_orthant_eq_lintegral (hS : S.PosDef) (b : Fin n → ℝ) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S {y | ∀ i, y i ≤ b i}
      = ∫⁻ x in Set.Iic b, ENNReal.ofReal (covDensity S x) := by
  have hf : Measurable
      (fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (covDensity S (WithLp.ofLp y))) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_covDensity_link S).comp (PiLp.continuous_ofLp 2 _)).measurable
  rw [multivariateGaussian_eq_withDensity_covDensity S hS,
    withDensity_apply _ (measurableSet_orthant_link b),
    lintegral_orthant_eq b
      (fun y => ENNReal.ofReal (covDensity S (WithLp.ofLp y))) hf]

/-- **The orthant mass of `N(0, S)` as an integral of the density.** -/
theorem multivariateGaussian_orthant_toReal_eq (hS : S.PosDef) (b : Fin n → ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S {y | ∀ i, y i ≤ b i}).toReal
      = ∫ x in Set.Iic b, covDensity S x := by
  rw [multivariateGaussian_orthant_eq_lintegral hS b,
    integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun x => (covDensity_pos hS x).le)
      (continuous_covDensity_link S).aestronglyMeasurable]

/-! ### The scalar covariance `v • 1` -/

section Scalar

variable {v : ℝ≥0}

/-- The scalar matrix `v • 1` is positive definite for `0 < v`. -/
theorem posDef_scalar_one (hv : 0 < v) :
    ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
  Matrix.PosDef.one.smul (by exact_mod_cast hv)

/-- The inverse of the scalar matrix `v • 1` is `v⁻¹ • 1`. -/
theorem inv_scalar_one (hv : 0 < v) :
    ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ = (v : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  refine Matrix.inv_eq_right_inv ?_
  rw [smul_mul_smul_comm, mul_one, mul_inv_cancel₀ hv', one_smul]

/-- The exponent of the density at the scalar matrix: `x ⬝ᵥ (v⁻¹ • 1) *ᵥ x = v⁻¹ * ∑ (x i)^2`. -/
theorem dotProduct_inv_scalar_one (x : Fin n → ℝ) :
    x ⬝ᵥ (((v : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x) = (v : ℝ)⁻¹ * ∑ i, x i ^ 2 := by
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  simp [dotProduct, pow_two]

/-- The normalising constant of the density at the scalar matrix is the `n`-th power of the
one-dimensional one. -/
theorem covDensity_scalar_const (hv : 0 < v) :
    (2 * Real.pi) ^ (-(n : ℝ) / 2) * (((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).det) ^
        (-(1 : ℝ) / 2)
      = ((√(2 * Real.pi * v))⁻¹) ^ n := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity [Real.pi_pos]
  have e1 : (√(2 * Real.pi * v))⁻¹ = (2 * Real.pi) ^ (-(1 / 2 : ℝ)) * (v : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity), Real.mul_rpow h2pi.le hv'.le]
  rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, e1, mul_pow,
    ← Real.rpow_mul_natCast h2pi.le, ← Real.rpow_mul_natCast hv'.le,
    ← Real.rpow_natCast_mul hv'.le]
  congr 2 <;> ring

/-- The density of `N(0, v I)` is the product of the one-dimensional Gaussian densities. -/
theorem covDensity_scalar (hv : 0 < v) (x : Fin n → ℝ) :
    covDensity ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) x = ∏ i, gaussianPDFReal 0 v (x i) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  unfold covDensity
  rw [inv_scalar_one hv, dotProduct_inv_scalar_one, covDensity_scalar_const hv]
  simp only [gaussianPDFReal, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum]
  congr 2
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp
  ring

/-- `Set.Iic b` as a product of coordinate half-lines: the integral of a product of functions of
single coordinates factors. -/
theorem integral_Iic_prod (f : ℝ → ℝ) (b : Fin n → ℝ) :
    ∫ x in Set.Iic b, ∏ i, f (x i) = ∏ i, ∫ y in Set.Iic (b i), f y := by
  rw [← Set.pi_univ_Iic b, volume_pi, Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod (fun _ => f)

/-- The one-dimensional Gaussian mass of a half-line as an integral of the density. -/
theorem gaussianReal_Iic_toReal (hv : 0 < v) (c : ℝ) :
    (gaussianReal 0 v (Set.Iic c)).toReal = ∫ y in Set.Iic c, gaussianPDFReal 0 v y := by
  rw [gaussianReal_apply_eq_integral 0 hv.ne' (Set.Iic c)]
  exact ENNReal.toReal_ofReal
    (integral_nonneg fun y => gaussianPDFReal_nonneg 0 v y)

/-- The orthant probability of `N(0, v I)` is the product of the marginal probabilities. -/
theorem multivariateGaussian_orthant_scalar (hv : 0 < v) (b : Fin n → ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
        ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) {y | ∀ i, y i ≤ b i}).toReal
      = ∏ i, (gaussianReal 0 v (Set.Iic (b i))).toReal := by
  rw [multivariateGaussian_orthant_toReal_eq (posDef_scalar_one hv) b]
  simp_rw [covDensity_scalar hv]
  rw [integral_Iic_prod (gaussianPDFReal 0 v) b]
  exact Finset.prod_congr rfl fun i _ => (gaussianReal_Iic_toReal hv (b i)).symm

end Scalar

/-! ### The starting value of the smart path and the final assembly -/

/-- **The orthant integral at the start of the smart path is the product of the marginal
masses**: `∫_{Iic b} covDensity (v • 1) = ∏ i, N(0, v)(Iic (b i))`. -/
theorem integral_orthant_smartPath_zero {m : ℕ} {v : ℝ≥0} {S : Matrix (Fin m) (Fin m) ℝ}
    (hv : 0 < v) (b : Fin m → ℝ) :
    (∫ x in Set.Iic b, covDensity (normalComparisonSmartPath (v : ℝ) S 0) x) =
      ∏ i, (gaussianReal 0 v (Set.Iic (b i))).toReal := by
  rw [normalComparisonSmartPath_zero,
    ← multivariateGaussian_orthant_toReal_eq (posDef_scalar_one hv) b]
  exact multivariateGaussian_orthant_scalar hv b

/-- **The final bound from the remaining two route facts.**  The density/scale step `F 0` is
discharged by `integral_orthant_smartPath_zero`; the hypotheses are the endpoint continuity
`hlim` and the interpolation `hinterp`. -/
theorem normalComparison_bound_of_limit_and_interpolation {m : ℕ} {v : ℝ≥0} (hv : 0 < v)
    {S : Matrix (Fin m) (Fin m) ℝ} (hnonneg : ∀ i j, 0 ≤ S i j) (b : Fin m → ℝ)
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
          Real.exp (-(b i ^ 2 + b j ^ 2) / (2 * (v : ℝ) * (1 + S i j / (v : ℝ)))) :=
  normalComparison_bound_of_interpolation (S := S) hv hnonneg b
    (integral_orthant_smartPath_zero hv b) hlim hinterp

end LatticeProb
