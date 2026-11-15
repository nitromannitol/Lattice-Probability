import LatticeProb.Analysis.PolarConePreimage
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Areas of polar cones -/

set_option autoImplicit false

open MeasureTheory Set
open scoped Pointwise ENNReal

namespace LatticeProb

/-- The polar Jacobian integrated over the unit radial interval. -/
theorem lintegral_unit_radius :
    ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal r = ENNReal.ofReal (1 / 2 : ℝ) := by
  have hi : IntegrableOn (fun r : ℝ => r) (Ioo 0 1) :=
    continuous_id.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_restrict_of_forall_mem measurableSet_Ioo fun r hr => hr.1.le)]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)]
  norm_num [integral_id]

/-- The planar area of the radial cone selected by a measurable set of arguments. -/
theorem volume_argument_radialCone {A : Set ℝ} (hA : MeasurableSet A) :
    volume (Ioo (0 : ℝ) 1 • {z : ℂ | ‖z‖ = 1 ∧ Complex.arg z ∈ A}) =
      ENNReal.ofReal (1 / 2 : ℝ) * volume (A ∩ Ioo (-Real.pi) Real.pi) := by
  let C : Set ℂ := Ioo (0 : ℝ) 1 • {z : ℂ | ‖z‖ = 1 ∧ Complex.arg z ∈ A}
  let B : Set ℝ := A ∩ Ioo (-Real.pi) Real.pi
  have hB : MeasurableSet B := hA.inter measurableSet_Ioo
  have hC : MeasurableSet C := by
    rw [show C = {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1 ∧ Complex.arg z ∈ A} from
      complex_argument_radialCone A]
    exact (measurableSet_lt measurable_const measurable_norm).inter
      ((measurableSet_lt measurable_norm measurable_const).inter (Complex.measurable_arg hA))
  have hpre : Complex.polarCoord.target ∩ Complex.polarCoord.symm ⁻¹' C = Ioo (0 : ℝ) 1 ×ˢ B :=
    polarCoord_preimage_argument_radialCone A
  calc
    volume C = (∫⁻ z, C.indicator (fun _ => (1 : ℝ≥0∞)) z) := by
      rw [lintegral_indicator hC, lintegral_one, Measure.restrict_apply_univ]
    _ = (∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 • C.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm p)) :=
      (Complex.lintegral_comp_polarCoord_symm _).symm
    _ = (∫⁻ p in Ioo (0 : ℝ) 1 ×ˢ B, ENNReal.ofReal p.1) := by
      have hc : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
        simp_rw [Complex.polarCoord_symm_apply]
        fun_prop
      have hm : MeasurableSet (Complex.polarCoord.symm ⁻¹' C) :=
        hC.preimage hc.measurable
      have heq : (fun p => ENNReal.ofReal p.1 •
          C.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm p)) =
          (Complex.polarCoord.symm ⁻¹' C).indicator (fun p => ENNReal.ofReal p.1) := by
        funext p
        by_cases hp : Complex.polarCoord.symm p ∈ C
        · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ Complex.polarCoord.symm ⁻¹' C from hp)]
          simp only [smul_eq_mul, mul_one]
        · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ Complex.polarCoord.symm ⁻¹' C from hp)]
          exact smul_zero _
      rw [heq, lintegral_indicator hm, Measure.restrict_restrict hm,
        inter_comm, hpre]
    _ = ENNReal.ofReal (1 / 2 : ℝ) * volume B := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      have hr : AEMeasurable (fun r : ℝ => ENNReal.ofReal r) (volume.restrict (Ioo 0 1)) :=
        ENNReal.measurable_ofReal.aemeasurable
      have hb : AEMeasurable (fun _ : ℝ => (1 : ℝ≥0∞)) (volume.restrict B) := aemeasurable_const
      simpa only [mul_one, lintegral_one, Measure.restrict_apply_univ, lintegral_unit_radius] using
        (lintegral_prod_mul hr hb)

end LatticeProb
