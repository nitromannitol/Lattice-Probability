import LatticeProb.Topology.TranslatedScalarBrownianCurveLaw
import Mathlib.Analysis.Normed.Lp.Matrix

/-! # Support of nondegenerate Brownian path laws -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal Matrix
open LatticeProb.UnboundedRayIntervalIntegrand
open ReflectedGMS.StatementIngredients

namespace LatticeProb.UnboundedRayCurveSpace

/-- A positive definite covariance has an invertible factor. -/
theorem isUnit_det_brownianFactor (target : AnisotropicBrownianTarget) :
    IsUnit target.factor.det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨ξ, hξ, hξA⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hpos := target.positiveDefinite.2 ξ hξ
  rw [target.covariance_eq, covarianceOfBrownianFactor] at hpos
  have h0 := congrFun hξA 0
  have h1 := congrFun hξA 1
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Pi.zero_apply] at h0 h1
  simp only [Fin.sum_univ_two, Matrix.mul_apply, Matrix.transpose_apply] at hpos
  refine absurd hpos (not_lt.mpr (le_of_eq ?_))
  linear_combination (ξ 0 * target.factor 0 0 + ξ 1 * target.factor 1 0) * h0 +
    (ξ 0 * target.factor 0 1 + ξ 1 * target.factor 1 1) * h1

/-- A nondegenerate anisotropic Brownian target has unbounded paths almost surely. -/
theorem ae_unbounded_range_anisotropicBrownian (target : AnisotropicBrownianTarget) :
    ∀ᵐ (f : Path 2) ∂(target.pathLaw : Measure (Path 2)),
      ¬ Bornology.IsBounded (Set.range f) := by
  rw [AnisotropicBrownianTarget.pathLaw, anisotropicBrownianLaw, ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff (measurable_linearImageBrownianPath _).aemeasurable
    (measurableSet_continuousMap_unbounded_range (0 : EuclideanSpace ℝ (Fin 2)))).2
  filter_upwards [BouRabeeGwynne.ae_unbounded_range_standardBrownian (by decide) target.isStandard]
    with f hf
  intro hb
  apply hf
  let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (Matrix.toEuclideanLin target.factor⁻¹).toContinuousLinearMap
  have hbounded := L.lipschitzWith.isBounded_image hb
  apply hbounded.subset
  rintro _ ⟨t, rfl⟩
  refine ⟨linearImageBrownianPath target.factor f t, ⟨t, rfl⟩, ?_⟩
  change Matrix.toEuclideanLin target.factor⁻¹ (linearImageBrownianPath target.factor f t) = f t
  apply PiLp.ext
  intro i
  change (target.factor⁻¹ *ᵥ (target.factor *ᵥ (fun j => f t j))) i = f t i
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_brownianFactor target),
    Matrix.one_mulVec]

/-- Translation preserves full unbounded support of the target law. -/
theorem ae_unbounded_range_translated_anisotropicBrownian
    (target : AnisotropicBrownianTarget) (z : EuclideanSpace ℝ (Fin 2)) :
    ∀ᵐ (f : Path 2) ∂((target.pathLaw : Measure (Path 2)).map (translatePath z)),
      ¬ Bornology.IsBounded (Set.range f) := by
  apply (ae_map_iff (continuous_translatePath z).measurable.aemeasurable
    (measurableSet_continuousMap_unbounded_range (0 : EuclideanSpace ℝ (Fin 2)))).2
  filter_upwards [ae_unbounded_range_anisotropicBrownian target] with f hf
  exact unbounded_range_translatePath z f hf

end LatticeProb.UnboundedRayCurveSpace
