import Mathlib
import LatticeProb.LQG.DyadicDilationMeasure
import LatticeProb.LQG.LocalMeasureKernel2
import LatticeProb.Gauss.GFFAffineInvariance

/-!
# Marks of the dilated whole-plane field

For a whole-plane Gaussian free field `h` and `c > 0`, the field `h(c ·) - h_c(0)` has pairings
`dilatedPairing` and circle averages `dilatedCirc`.  Almost surely:

* the pairing of the dilated field against the rescaled test function `x ↦ c² φ(c x)` with `∫ φ = 0` is the
  pairing `(h, φ)` of the original field (`ae_dilatedPairing_scaled`);
* the circle average of the dilated field at radius `c⁻¹` about the origin is `- h_c(0)`
  (`ae_dilatedCirc_inv`).
-/

open MeasureTheory

namespace LatticeProb.LQG.DyadicDilation

open LatticeProb.Gauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The dilated pairing against `x ↦ c² φ(c x)` is the original pairing against `φ` when `∫ φ = 0`. -/
theorem ae_dilatedPairing_scaled (hh : IsWholePlaneGFF P hC hcirc) {c : ℝ} (hc : 0 < c) {φ : ℂ → ℝ}
    (hφ : IsTestFunction Set.univ φ) (hφ0 : ∫ x, φ x = 0) :
    ∀ᵐ ω ∂P, dilatedPairing hC hcirc c ω (fun x => c ^ 2 * φ (c • x)) = hC ω φ := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hint : ∫ x, c ^ 2 * φ (c • x) = 0 := by
    have h := Measure.integral_comp_smul (μ := (volume : Measure ℂ)) φ c
    rw [integral_const_mul, h, hφ0, smul_zero, mul_zero]
  have hfun : (fun y : ℂ => c ^ 2 * φ (c • (y / (c : ℂ)))) = fun y => c ^ 2 * φ y + 0 * φ y := by
    funext y
    rw [Complex.real_smul, mul_div_cancel₀ _ hc', zero_mul, add_zero]
  filter_upwards [LatticeProb.LocalMeasureKernel.ae_pairing_linear_combination hh hφ hφ (c ^ 2) 0] with ω hω
  unfold dilatedPairing
  rw [hint, mul_zero, sub_zero]
  show (c ^ 2)⁻¹ * hC ω (fun y : ℂ => c ^ 2 * φ (c • (y / (c : ℂ)))) = hC ω φ
  rw [hfun, hω]
  have : c ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The circle average of the dilated field at radius `c⁻¹` about the origin is `- h_c(0)`. -/
theorem ae_dilatedCirc_inv (hh : IsWholePlaneGFF P hC hcirc) {c : ℝ} (hc : 0 < c) :
    ∀ᵐ ω ∂P, dilatedCirc hcirc c ω c⁻¹ 0 = - hcirc ω c 0 := by
  filter_upwards [hh.ae_circleAverage_one_zero] with ω hω
  unfold dilatedCirc
  rw [mul_inv_cancel₀ hc.ne', mul_zero, hω]
  ring

end LatticeProb.LQG.DyadicDilation
