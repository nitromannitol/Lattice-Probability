import LatticeProb.Analysis.WedgeArcWeakEigenfunction

/-! # Integrability of angular functions on an arc -/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace LatticeProb

/-- A continuous function of the argument is integrable on a finite arc. -/
theorem integrable_arg_wedgeArcSurfaceMeasure {θ : ℝ} (hθ' : θ ≤ 2 * Real.pi) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (fun z : sphere (0 : ℂ) 1 => f (Complex.arg z))
      (wedgeArcSurfaceMeasure θ) := by
  have hm : Measurable (fun z : sphere (0 : ℂ) 1 => f (Complex.arg z)) :=
    hf.measurable.comp (Complex.measurable_arg.comp measurable_subtype_coe)
  rw [wedgeArcSurfaceMeasure, ← map_unitCircleParam_restrict hθ',
    integrable_map_measure hm.aestronglyMeasurable measurable_unitCircleParam.aemeasurable]
  have hi : IntegrableOn f (Ioc (-θ / 2) (θ / 2)) :=
    hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  apply hi.congr_fun_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simp only [Function.comp_apply, unitCircleParam, arg_circleMap_mem_wedge hθ' hx]

end LatticeProb
