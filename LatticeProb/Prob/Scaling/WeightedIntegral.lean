/- Stability of weighted integrals under uniform perturbations of the coefficient.

Moved from Parking-Sharpness.
-/
import Mathlib
open MeasureTheory
namespace LatticeProb.Scaling.WeightedIntegral

/-- A uniform error in the test coefficient is controlled by the absolute mass of the weight. -/
theorem abs_pairing_sub_le {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {u f g : E → ℝ} (hu : Integrable u μ)
    (hf : Integrable (fun x => u x * f x) μ)
    (hg : Integrable (fun x => u x * g x) μ)
    {ε : ℝ} (hfg : ∀ᵐ x ∂μ, |f x - g x| ≤ ε) :
    |(∫ x, u x * f x ∂μ) - ∫ x, u x * g x ∂μ| ≤ ε * ∫ x, |u x| ∂μ := by
  rw [← integral_sub hf hg, ← integral_const_mul]
  apply abs_integral_le_integral_abs.trans
  apply integral_mono_ae (hf.sub hg).abs (hu.abs.const_mul ε)
  filter_upwards [hfg] with x hx
  change |u x * f x - u x * g x| ≤ ε * |u x|
  rw [← mul_sub, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hx (abs_nonneg (u x))
end LatticeProb.Scaling.WeightedIntegral
