import LatticeProb.Analysis.WedgeSurfaceIntegral

/-! # Angular parametrization of circle surface measure -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb

/-- The unit circle, parametrized by its angle. -/
noncomputable def unitCircleParam (x : ℝ) : sphere (0 : ℂ) 1 :=
  ⟨circleMap 0 1 x, by simp [norm_circleMap_zero]⟩

theorem measurable_unitCircleParam : Measurable unitCircleParam := by
  apply Measurable.subtype_mk
  exact (continuous_circleMap 0 1).measurable

/-- The pushforward of angular Lebesgue measure is surface measure on the arc. -/
theorem map_unitCircleParam_restrict {θ : ℝ} (hθ : θ ≤ 2 * Real.pi) :
    Measure.map unitCircleParam (volume.restrict (Ioc (-θ / 2) (θ / 2))) =
      (volume : Measure ℂ).toSphere.restrict
        {z : sphere (0 : ℂ) 1 | Complex.arg z ∈ Ioo (-θ / 2) (θ / 2)} := by
  apply (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).map_injective
  rw [Measure.map_map measurable_subtype_coe measurable_unitCircleParam,
    map_restrict_complex_toSphere_wedge hθ]
  rfl

/-- Surface Lp functions pull back to Lp functions of angle. -/
theorem memLp_comp_unitCircleParam {θ : ℝ} (hθ : θ ≤ 2 * Real.pi)
    {p : ℝ≥0∞} {f : sphere (0 : ℂ) 1 → ℂ}
    (hf : MemLp f p ((volume : Measure ℂ).toSphere.restrict
      {z : sphere (0 : ℂ) 1 | Complex.arg z ∈ Ioo (-θ / 2) (θ / 2)})) :
    MemLp (f ∘ unitCircleParam) p (volume.restrict (Ioc (-θ / 2) (θ / 2))) := by
  apply MemLp.comp_of_map (f := unitCircleParam) ?_ measurable_unitCircleParam.aemeasurable
  rwa [map_unitCircleParam_restrict hθ]

/-- Integrating an almost-everywhere strongly measurable function on the arc is
integration of its angular pullback. -/
theorem integral_comp_unitCircleParam {θ : ℝ} (hθ : θ ≤ 2 * Real.pi)
    {f : sphere (0 : ℂ) 1 → ℂ}
    (hf : AEStronglyMeasurable f ((volume : Measure ℂ).toSphere.restrict
      {z : sphere (0 : ℂ) 1 | Complex.arg z ∈ Ioo (-θ / 2) (θ / 2)})) :
    (∫ z, f z ∂((volume : Measure ℂ).toSphere.restrict
      {z : sphere (0 : ℂ) 1 | Complex.arg z ∈ Ioo (-θ / 2) (θ / 2)})) =
      ∫ x in Ioc (-θ / 2) (θ / 2), f (unitCircleParam x) := by
  rw [← map_unitCircleParam_restrict hθ] at hf ⊢
  exact integral_map measurable_unitCircleParam.aemeasurable hf

end LatticeProb
