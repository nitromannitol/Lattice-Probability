import LatticeProb.Analysis.WedgeAngularIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Angular integrals on a unit-circle arc -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- The image of ordinary angular measure on a symmetric unit-circle arc. -/
noncomputable def wedgeArcMeasure (θ : ℝ) : Measure ℂ :=
  Measure.map (circleMap 0 1) (volume.restrict (Ioc (-θ / 2) (θ / 2)))

/-- The normalized positive sine mode expressed using the principal argument. -/
noncomputable def wedgeArcMode (θ : ℝ) (z : ℂ) : ℝ :=
  Real.sqrt (2 / θ) * wedgeAngularMode θ z.arg

theorem arg_circleMap_mem_wedge {θ x : ℝ} (hθ : θ ≤ 2 * Real.pi)
    (hx : x ∈ Ioc (-θ / 2) (θ / 2)) : (circleMap 0 1 x).arg = x := by
  have h : x ∈ Ioc (-Real.pi) Real.pi := by
    constructor <;> linarith [hx.1, hx.2]
  have hh : x ∈ Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    constructor <;> linarith [h.1, h.2]
  simpa only [circleMap_zero, Complex.ofReal_one, one_mul, Complex.arg_exp_mul_I] using
    (toIocMod_eq_self Real.two_pi_pos).2 hh

/-- The angular parameter has unit speed on the circle. -/
theorem norm_deriv_unit_circleMap (x : ℝ) : ‖deriv (circleMap 0 1) x‖ = 1 := by
  simp only [deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I, abs_one, mul_one]

/-- The normalized mode has unit squared integral for the angular image measure. -/
theorem integral_wedgeArcMode_sq {θ : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi) :
    (∫ z, wedgeArcMode θ z ^ 2 ∂wedgeArcMeasure θ) = 1 := by
  have hm : Measurable (fun z : ℂ => wedgeArcMode θ z ^ 2) := by
    unfold wedgeArcMode wedgeAngularMode
    fun_prop (disch := exact Complex.measurable_arg)
  rw [wedgeArcMeasure, integral_map (by fun_prop) hm.aestronglyMeasurable]
  have heq : (fun x => wedgeArcMode θ (circleMap 0 1 x) ^ 2) =ᵐ[volume.restrict (Ioc (-θ / 2) (θ / 2))]
      (fun x => (Real.sqrt (2 / θ) * wedgeAngularMode θ x) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    simp only [wedgeArcMode, arg_circleMap_mem_wedge hθ' hx]
  rw [integral_congr_ae heq, ← intervalIntegral.integral_of_le (by linarith : -θ / 2 ≤ θ / 2)]
  exact integral_normalized_wedgeAngularMode_sq hθ

/-- The integral of the normalized mode for the angular image measure. -/
theorem integral_wedgeArcMode {θ : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi) :
    (∫ z, wedgeArcMode θ z ∂wedgeArcMeasure θ) =
      Real.sqrt (2 / θ) * (2 * θ / Real.pi) := by
  have hm : Measurable (wedgeArcMode θ) := by
    unfold wedgeArcMode wedgeAngularMode
    fun_prop (disch := exact Complex.measurable_arg)
  rw [wedgeArcMeasure, integral_map (by fun_prop) hm.aestronglyMeasurable]
  have heq : (fun x => wedgeArcMode θ (circleMap 0 1 x)) =ᵐ[volume.restrict (Ioc (-θ / 2) (θ / 2))]
      (fun x => Real.sqrt (2 / θ) * wedgeAngularMode θ x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    simp only [wedgeArcMode, arg_circleMap_mem_wedge hθ' hx]
  rw [integral_congr_ae heq, ← intervalIntegral.integral_of_le (by linarith : -θ / 2 ≤ θ / 2)]
  exact integral_normalized_wedgeAngularMode hθ

end LatticeProb
