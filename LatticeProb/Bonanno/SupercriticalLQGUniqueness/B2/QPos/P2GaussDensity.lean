/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2GaussDensity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2GaussLinAlg

 









set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal MatrixOrder

namespace SupercriticalLQGUniqueness.B2.QPos

 
theorem withDensity_map_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞) :
    (μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, MeasurableEquiv.restrict_map, lintegral_map_equiv]
  simp

variable {V : Type*} [Fintype V] [DecidableEq V]

 
theorem pi_gaussianReal_eq_withDensity :
    Measure.pi (fun _ : V => gaussianReal 0 1) =
      volume.withDensity (fun x : V → ℝ => ENNReal.ofReal (∏ v, gaussianPDFReal 0 1 (x v))) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hind : ∀ x : V → ℝ, (Set.univ.pi s).indicator
      (fun x : V → ℝ => ENNReal.ofReal (∏ v, gaussianPDFReal 0 1 (x v))) x =
      ENNReal.ofReal (∏ v, (s v).indicator (gaussianPDFReal 0 1) (x v)) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      congr 1
      apply Finset.prod_congr rfl
      intro v _
      rw [Set.indicator_of_mem (hx v (Set.mem_univ v))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨v, hv⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ v) (Set.indicator_of_notMem hv _),
        ENNReal.ofReal_zero]
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [hind]
  have hint : ∀ v, Integrable ((s v).indicator (gaussianPDFReal 0 1)) volume := fun v =>
    (integrable_gaussianPDFReal 0 1).indicator (hs v)
  have hnn : ∀ x : V → ℝ, 0 ≤ ∏ v, (s v).indicator (gaussianPDFReal 0 1) (x v) := fun x =>
    Finset.prod_nonneg fun v _ => Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _
  rw [← ofReal_integral_eq_lintegral_ofReal (by
      rw [volume_pi]; exact Integrable.fintype_prod hint)
    (Filter.Eventually.of_forall hnn), integral_fintype_prod_volume_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun v _ => integral_nonneg
      fun y => Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _)]
  apply Finset.prod_congr rfl
  intro v _
  rw [gaussianReal_apply 0 one_ne_zero, integral_indicator (hs v),
    ofReal_integral_eq_lintegral_ofReal ((integrable_gaussianPDFReal 0 1).integrableOn)
      (Filter.Eventually.of_forall fun y => gaussianPDFReal_nonneg 0 1 y)]
  rfl

 
theorem stdGaussian_eq_withDensity :
    stdGaussian (EuclideanSpace ℝ V) =
      volume.withDensity (fun y : EuclideanSpace ℝ V =>
        ENNReal.ofReal (∏ v, gaussianPDFReal 0 1 (y v))) := by
  rw [← map_pi_eq_stdGaussian, pi_gaussianReal_eq_withDensity]
  have hvol : (volume : Measure (V → ℝ)).map ⇑(MeasurableEquiv.toLp 2 (V → ℝ)) = volume :=
    (PiLp.volume_preserving_toLp V).map_eq
  rw [show (WithLp.toLp 2 : (V → ℝ) → EuclideanSpace ℝ V) = ⇑(MeasurableEquiv.toLp 2 (V → ℝ))
    from rfl, withDensity_map_measurableEquiv, hvol]
  rfl

 
theorem prod_gaussianPDFReal (y : V → ℝ) :
    ∏ v, gaussianPDFReal 0 1 (y v) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card V * Real.exp (-(1 / 2) * (y ⬝ᵥ y)) := by
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
  congr 2
  simp only [dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

 
theorem multivariateGaussian_eq_withDensity {S : Matrix V V ℝ} (hS : S.PosDef)
    (m : EuclideanSpace ℝ V) :
    ∃ C : ℝ, 0 < C ∧ multivariateGaussian m S =
      volume.withDensity (fun z : EuclideanSpace ℝ V => ENNReal.ofReal (C *
        Real.exp (-(1 / 2) * ((z - m).ofLp ⬝ᵥ (S⁻¹ *ᵥ (z - m).ofLp))))) := by
  set A := CFC.sqrt S with hA
  have hAA : A * A = S := cfcSqrt_mul_self hS.posSemidef
  have hdetA : IsUnit A.det := by
    have : IsUnit (A * A).det := by rw [hAA]; exact (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit
    rw [Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdetA
  have hinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hdetA
  
  let L : EuclideanSpace ℝ V ≃L[ℝ] EuclideanSpace ℝ V :=
    ContinuousLinearEquiv.equivOfInverse (toEuclideanCLM (𝕜 := ℝ) A)
      (toEuclideanCLM (𝕜 := ℝ) A⁻¹)
      (fun x => by
        show (toEuclideanCLM (𝕜 := ℝ) A⁻¹ * toEuclideanCLM (𝕜 := ℝ) A) x = x
        rw [← map_mul, hinvA, map_one]; rfl)
      (fun x => by
        show (toEuclideanCLM (𝕜 := ℝ) A * toEuclideanCLM (𝕜 := ℝ) A⁻¹) x = x
        rw [← map_mul, hAinv, map_one]; rfl)
  let T : EuclideanSpace ℝ V ≃ᵐ EuclideanSpace ℝ V :=
    L.toHomeomorph.toMeasurableEquiv.trans (MeasurableEquiv.addLeft m)
  have hT : (fun x => m + toEuclideanCLM (𝕜 := ℝ) A x) = ⇑T := rfl
  have hdetL : LinearMap.det (L : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V) ≠ 0 :=
    (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero
  set c : ℝ≥0∞ := ENNReal.ofReal |(LinearMap.det (L : EuclideanSpace ℝ V →ₗ[ℝ]
    EuclideanSpace ℝ V))⁻¹| with hc
  have hvolT : (volume : Measure (EuclideanSpace ℝ V)).map T = c • volume := by
    have h1 := Measure.map_linearMap_addHaar_eq_smul_addHaar
      (volume : Measure (EuclideanSpace ℝ V)) hdetL
    have h2 : (volume : Measure (EuclideanSpace ℝ V)).map T =
        ((volume : Measure (EuclideanSpace ℝ V)).map L).map (m + ·) := by
      rw [Measure.map_map (measurable_const_add m) L.continuous.measurable]
      rfl
    rw [h2, show (⇑L : EuclideanSpace ℝ V → EuclideanSpace ℝ V) =
      ⇑(L : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V) from rfl, h1, Measure.map_smul,
      (measurePreserving_add_left volume m).map_eq]
    exact (measurable_const_add m).aemeasurable
  have hcpos : 0 < c.toReal := by
    rw [hc, ENNReal.toReal_ofReal (abs_nonneg _)]
    exact abs_pos.mpr (inv_ne_zero hdetL)
  refine ⟨c.toReal * (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card V,
    mul_pos hcpos (pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))) _), ?_⟩
  rw [multivariateGaussian, ← hA, hT, stdGaussian_eq_withDensity,
    withDensity_map_measurableEquiv, hvolT, withDensity_smul_measure,
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext z
  simp only [Pi.smul_apply, Function.comp, smul_eq_mul]
  rw [mul_assoc, ENNReal.ofReal_mul hcpos.le,
    ENNReal.ofReal_toReal (show c ≠ ⊤ from ENNReal.ofReal_ne_top)]
  congr 2
  
  have hTs : (T.symm z).ofLp = A⁻¹ *ᵥ (z - m).ofLp := by
    have : T (WithLp.toLp 2 (A⁻¹ *ᵥ (z - m).ofLp)) = z := by
      show m + toEuclideanCLM (𝕜 := ℝ) A (WithLp.toLp 2 (A⁻¹ *ᵥ (z - m).ofLp)) = z
      rw [toEuclideanCLM_toLp, Matrix.mulVec_mulVec, hAinv, Matrix.one_mulVec]
      simp
    rw [(T.symm_apply_eq).mpr this.symm]
  rw [prod_gaussianPDFReal (T.symm z).ofLp, hTs]
  have hAT : Aᵀ = A := cfcSqrt_transpose S
  have hquad : (A⁻¹ *ᵥ (z - m).ofLp) ⬝ᵥ (A⁻¹ *ᵥ (z - m).ofLp) =
      (z - m).ofLp ⬝ᵥ (S⁻¹ *ᵥ (z - m).ofLp) := by
    rw [dotProduct_mulVec_symm _ (by rw [Matrix.transpose_nonsing_inv, hAT]),
      Matrix.mulVec_mulVec, ← Matrix.mul_inv_rev, hAA]
  rw [hquad]

end SupercriticalLQGUniqueness.B2.QPos
