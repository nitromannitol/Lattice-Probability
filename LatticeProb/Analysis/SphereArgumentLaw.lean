import LatticeProb.Analysis.PolarConeVolume
import LatticeProb.Analysis.WedgeCircleArgument
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! # Argument distribution of the surface measure on the complex unit circle -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped Pointwise ENNReal

namespace LatticeProb

/-- The principal argument of complex circle surface measure has Lebesgue distribution. -/
theorem map_arg_complex_toSphere :
    Measure.map (fun z : sphere (0 : ℂ) 1 => Complex.arg z)
        (volume : Measure ℂ).toSphere =
      volume.restrict (Ioc (-Real.pi) Real.pi) := by
  ext A hA
  change (Measure.map (Complex.arg ∘ Subtype.val) (volume : Measure ℂ).toSphere) A = _
  rw [Measure.map_apply (Complex.measurable_arg.comp measurable_subtype_coe) hA,
    Measure.toSphere_apply' _ (hA.preimage (Complex.measurable_arg.comp measurable_subtype_coe)),
    Complex.finrank_real_complex]
  have himage : (Subtype.val '' {z : sphere (0 : ℂ) 1 | Complex.arg z ∈ A}) =
      {z : ℂ | ‖z‖ = 1 ∧ Complex.arg z ∈ A} := by
    ext z
    constructor
    · rintro ⟨⟨w, hw⟩, ha, rfl⟩
      exact ⟨by simpa [mem_sphere, dist_zero_right] using hw, ha⟩
    · rintro ⟨hz, ha⟩
      exact ⟨⟨z, by simpa [mem_sphere, dist_zero_right] using hz⟩, ha, rfl⟩
  change (2 : ℝ≥0∞) * volume (Ioo (0 : ℝ) 1 •
    (Subtype.val '' {z : sphere (0 : ℂ) 1 | Complex.arg z ∈ A})) = _
  rw [himage, volume_argument_radialCone hA]
  have hh : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ) = 1 := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [← mul_assoc, hh, one_mul, ← Measure.restrict_apply hA,
    restrict_Ioo_eq_restrict_Ioc, Measure.restrict_apply hA]

/-- Angular measure for a full turn is surface measure on the unit circle. -/
theorem map_coe_complex_toSphere :
    Measure.map (Subtype.val : sphere (0 : ℂ) 1 → ℂ) (volume : Measure ℂ).toSphere =
      wedgeArcMeasure (2 * Real.pi) := by
  apply eq_wedgeArcMeasure_of_map_arg
  · apply (MeasureTheory.ae_map_iff measurable_subtype_coe.aemeasurable
      ((measurableSet_singleton (1 : ℝ)).preimage measurable_norm)).2
    exact Filter.Eventually.of_forall fun z => mem_sphere_zero_iff_norm.1 z.property
  · rw [Measure.map_map Complex.measurable_arg measurable_subtype_coe]
    convert map_arg_complex_toSphere using 1 <;> congr 2 <;> ring

end LatticeProb
