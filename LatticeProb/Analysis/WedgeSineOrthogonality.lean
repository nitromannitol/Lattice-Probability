import LatticeProb.Analysis.WedgeSurfaceIntegral
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen5

/-! # Orthogonality of angular modes on a circular arc -/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace LatticeProb

/-- The normalized sine modes are orthogonal for the surface measure on an arc. -/
theorem integral_sinMode_mul_sinMode_toSphere {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 2 * Real.pi) {j k : ℕ} (hk : k ≠ 0) :
    (∫ z : sphere (0 : ℂ) 1,
      (Real.sqrt (2 / θ) * LQGMetric.HeatSq.sinMode (-θ / 2) θ j z.val.arg) *
      (Real.sqrt (2 / θ) * LQGMetric.HeatSq.sinMode (-θ / 2) θ k z.val.arg)
      ∂((volume : Measure ℂ).toSphere.restrict
        {z : sphere (0 : ℂ) 1 | Complex.arg z ∈ Ioo (-θ / 2) (θ / 2)})) =
      if j = k then 1 else 0 := by
  let f : ℂ → ℝ := fun z =>
    (Real.sqrt (2 / θ) * LQGMetric.HeatSq.sinMode (-θ / 2) θ j z.arg) *
    (Real.sqrt (2 / θ) * LQGMetric.HeatSq.sinMode (-θ / 2) θ k z.arg)
  have hm : Measurable f := by
    dsimp [f, LQGMetric.HeatSq.sinMode]
    fun_prop (disch := exact Complex.measurable_arg)
  change (∫ z : sphere (0 : ℂ) 1, f z.val ∂_) = _
  rw [← integral_map measurable_subtype_coe.aemeasurable hm.aestronglyMeasurable,
    map_restrict_complex_toSphere_wedge hθ', wedgeArcMeasure,
    integral_map (by fun_prop) hm.aestronglyMeasurable]
  have heq : (fun x => f (circleMap 0 1 x)) =ᵐ[volume.restrict (Ioc (-θ / 2) (θ / 2))]
      (fun x => (2 / θ) * (LQGMetric.HeatSq.sinMode (-θ / 2) θ j x *
        LQGMetric.HeatSq.sinMode (-θ / 2) θ k x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    simp only [f, arg_circleMap_mem_wedge hθ' hx]
    calc
      _ = (Real.sqrt (2 / θ)) ^ 2 *
          (LQGMetric.HeatSq.sinMode (-θ / 2) θ j x *
           LQGMetric.HeatSq.sinMode (-θ / 2) θ k x) := by ring
      _ = _ := by rw [Real.sq_sqrt (show 0 ≤ 2 / θ by positivity)]
  rw [integral_congr_ae heq, integral_const_mul, integral_Ioc_eq_integral_Ioo]
  have hinterval : -θ / 2 + θ = θ / 2 := by ring
  rw [← hinterval, LQGMetric.HeatSq.integral_sinMode_mul_sinMode hθ hk]
  split_ifs
  · field_simp
  · simp only [mul_zero]

end LatticeProb
