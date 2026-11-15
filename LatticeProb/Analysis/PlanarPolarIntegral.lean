import LatticeProb.Analysis.ViscositySubMean

/-! # Polar integration on the complex plane -/

set_option autoImplicit false

open MeasureTheory Metric Set

namespace LatticeProb

/-- Planar Lebesgue integration in polar coordinates, with unit-circle surface
measure and the radial density `r`. -/
theorem integral_complex_polar {f : ℂ → ℝ} (hf : Integrable f) :
    ∫ z, f z = ∫ r in Ioi (0 : ℝ), r * ∫ u : sphere (0 : ℂ) 1,
      f (r • (u : ℂ)) ∂((volume : Measure ℂ).toSphere) := by
  rw [Ishii.integral_polar volume f,
    integral_prod_symm _ (Ishii.integrable_polar volume hf)]
  simp only [Complex.finrank_real_complex, Nat.reduceSub, Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi
      (fun r : ℝ => (Real.toNNReal (r ^ 1)) • ∫ u : sphere (0 : ℂ) 1,
        f (r • (u : ℂ)) ∂((volume : Measure ℂ).toSphere))]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp only [pow_one, NNReal.smul_def, Real.coe_toNNReal r hr.le, smul_eq_mul]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

end LatticeProb
