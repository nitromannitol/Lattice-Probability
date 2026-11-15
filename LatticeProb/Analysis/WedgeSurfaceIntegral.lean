import LatticeProb.Analysis.SphereArgumentLaw
import LatticeProb.Analysis.WedgeArcRestriction

/-! # Integrals of angular modes against circle surface measure -/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace LatticeProb

/-- Restricting unit-circle surface measure to a symmetric arc and mapping it
into the plane gives the ordinary angular measure of the arc. -/
theorem map_restrict_complex_toSphere_wedge {θ : ℝ} (hθ : θ ≤ 2 * Real.pi) :
    Measure.map (Subtype.val : sphere (0 : ℂ) 1 → ℂ)
        ((volume : Measure ℂ).toSphere.restrict
          {z : sphere (0 : ℂ) 1 | Complex.arg z ∈ Ioo (-θ / 2) (θ / 2)}) =
      wedgeArcMeasure θ := by
  rw [wedgeArcMeasure_eq_restrict_full hθ, ← map_coe_complex_toSphere]
  symm
  exact Measure.restrict_map measurable_subtype_coe
    (s := {z : ℂ | Complex.arg z ∈ Ioo (-θ / 2) (θ / 2)})
    (Complex.measurable_arg measurableSet_Ioo)

/-- The normalized positive angular mode has unit squared integral over the
symmetric arc with respect to circle surface measure. -/
theorem integral_wedgeArcMode_sq_toSphere {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 2 * Real.pi) :
    (∫ z : sphere (0 : ℂ) 1, wedgeArcMode θ z ^ 2 ∂((volume : Measure ℂ).toSphere.restrict
      {z : sphere (0 : ℂ) 1 | Complex.arg z ∈ Ioo (-θ / 2) (θ / 2)})) = 1 := by
  have hm : Measurable (fun z : ℂ => wedgeArcMode θ z ^ 2) := by
    unfold wedgeArcMode wedgeAngularMode
    fun_prop (disch := exact Complex.measurable_arg)
  rw [← integral_map measurable_subtype_coe.aemeasurable hm.aestronglyMeasurable,
    map_restrict_complex_toSphere_wedge hθ']
  exact integral_wedgeArcMode_sq hθ hθ'

/-- The integral of the normalized positive angular mode over the symmetric
arc with respect to circle surface measure. -/
theorem integral_wedgeArcMode_toSphere {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 2 * Real.pi) :
    (∫ z : sphere (0 : ℂ) 1, wedgeArcMode θ z ∂((volume : Measure ℂ).toSphere.restrict
      {z : sphere (0 : ℂ) 1 | Complex.arg z ∈ Ioo (-θ / 2) (θ / 2)})) =
      Real.sqrt (2 / θ) * (2 * θ / Real.pi) := by
  have hm : Measurable (wedgeArcMode θ) := by
    unfold wedgeArcMode wedgeAngularMode
    fun_prop (disch := exact Complex.measurable_arg)
  rw [← integral_map measurable_subtype_coe.aemeasurable hm.aestronglyMeasurable,
    map_restrict_complex_toSphere_wedge hθ']
  exact integral_wedgeArcMode hθ hθ'

end LatticeProb
