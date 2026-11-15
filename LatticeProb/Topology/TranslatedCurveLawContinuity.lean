import LatticeProb.Topology.AnisotropicBrownianCurveSupport
import LatticeProb.Prob.ContinuousPushforwardFamily

/-! # Continuity of translated local curve laws -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal
open LatticeProb.UnboundedRayIntervalIntegrand

namespace LatticeProb.UnboundedRayCurveSpace

noncomputable section

local instance {d : ℕ} : MeasurableSpace (UnboundedRayCurveSpace d) := borel _
local instance {d : ℕ} : BorelSpace (UnboundedRayCurveSpace d) := ⟨rfl⟩
attribute [local instance] dUnifMetricSpace

/-- Translation of an unbounded continuous path remains unbounded. -/
def translateRay {d : ℕ} (z : EuclideanSpace ℝ (Fin d)) (f : UnboundedRay d) :
    UnboundedRay d :=
  ⟨translatePath z f.1, unbounded_range_translatePath z f.1 f.2⟩

/-- Translation is jointly continuous in the starting point and the ray. -/
theorem continuous_translateRay {d : ℕ} :
    Continuous (fun p : UnboundedRay d × EuclideanSpace ℝ (Fin d) =>
      translateRay p.2 p.1) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (UnboundedRay d × EuclideanSpace ℝ (Fin d)) × ℝ≥0 =>
    p.1.2 + p.1.1.1 p.2)
  fun_prop

/-- The local curve law obtained by translating a path law. -/
def translatedCurveProbability {d : ℕ} (μ : Measure (Path d))
    [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ (f : Path d) ∂μ, ¬ Bornology.IsBounded (Set.range f))
    (z : EuclideanSpace ℝ (Fin d)) : ProbabilityMeasure (UnboundedRayCurveSpace d) := by
  let : IsProbabilityMeasure (μ.map (translatePath z)) :=
    (Measure.isProbabilityMeasure_map_iff (continuous_translatePath z).measurable.aemeasurable).2 inferInstance
  have hsupport : ∀ᵐ (f : Path d) ∂(μ.map (translatePath z)),
      ¬ Bornology.IsBounded (Set.range f) := by
    apply (ae_map_iff (continuous_translatePath z).measurable.aemeasurable
      (measurableSet_continuousMap_unbounded_range 0)).2
    filter_upwards [hμ] with f hf
    exact unbounded_range_translatePath z f hf
  exact ⟨curveLaw (μ.map (translatePath z)) hsupport, inferInstance⟩

/-- Translating a fixed probability law on unbounded paths gives a weakly
continuous family of local curve laws. -/
theorem continuous_translated_curveLaw {d : ℕ} (μ : Measure (Path d))
    [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ (f : Path d) ∂μ, ¬ Bornology.IsBounded (Set.range f)) :
    Continuous (translatedCurveProbability μ hμ) := by
  let ν : Measure (UnboundedRay d) := supportedLaw μ _ hμ
  have hν : ν.map Subtype.val = μ := map_supportedLaw μ _ hμ
  let : IsProbabilityMeasure ν := supportedLaw_isProbability μ _ hμ
  let νp : ProbabilityMeasure (UnboundedRay d) := ⟨ν, inferInstance⟩
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin d) =>
      νp.map (fun f => project (translateRay z f))) := by
    exact continuous_probabilityMeasure_map_family (μ := fun _ => νp) continuous_const
      (F := fun p : UnboundedRay d × EuclideanSpace ℝ (Fin d) =>
        project (translateRay p.2 p.1)) (continuous_project.comp continuous_translateRay)
  convert hc using 1
  funext z
  apply Subtype.ext
  change curveLaw (μ.map (translatePath z)) _ = ν.map (fun f => project (translateRay z f))
  have ht : Measurable (translateRay z) :=
    (continuous_translateRay.comp (continuous_id.prodMk continuous_const)).measurable
  have hlift : (ν.map (translateRay z)).map Subtype.val = μ.map (translatePath z) := by
    rw [Measure.map_map measurable_subtype_coe ht, ← hν,
      Measure.map_map (continuous_translatePath z).measurable measurable_subtype_coe]
    rfl
  rw [← map_project_eq_curveLaw _ _ _ hlift,
    Measure.map_map continuous_project.measurable ht]
  rfl

/-- The local curve law of a nondegenerate anisotropic Brownian motion varies
continuously with its starting point. -/
theorem continuous_translated_anisotropicBrownian_curveLaw
    (target : ReflectedGMS.StatementIngredients.AnisotropicBrownianTarget) :
    Continuous (translatedCurveProbability (target.pathLaw : Measure (Path 2))
      (ae_unbounded_range_anisotropicBrownian target)) :=
  continuous_translated_curveLaw _ _

end
end LatticeProb.UnboundedRayCurveSpace
