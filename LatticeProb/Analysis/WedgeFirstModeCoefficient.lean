import LatticeProb.Analysis.WedgeSurfaceIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # First angular mode coefficient for a planar wedge -/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace LatticeProb

/-- The integral of the normalized positive mode multiplied by its value on
    the axis has a simple form. -/
theorem wedge_first_mode_axis_factor {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 2 * Real.pi) :
    (∫ z : sphere (0 : ℂ) 1, wedgeArcMode θ z ∂((volume : Measure ℂ).toSphere.restrict
      {z : sphere (0 : ℂ) 1 | Complex.arg z ∈ Ioo (-θ / 2) (θ / 2)})) *
      (Real.sqrt (2 / θ) * wedgeAngularMode θ 0) = 4 / Real.pi := by
  rw [integral_wedgeArcMode_toSphere hθ hθ', wedgeAngularMode_zero hθ, mul_one]
  have hs : Real.sqrt (2 / θ) ^ 2 = 2 / θ := Real.sq_sqrt (by positivity)
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have ht : θ ≠ 0 := ne_of_gt hθ
  field_simp at hs ⊢
  nlinarith

/-- Evaluating the normalized first-mode expression at the symmetry axis
    simplifies its angular factor. -/
theorem wedge_first_mode_coefficient {θ t : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 2 * Real.pi) :
    (Real.Gamma ((Real.pi / θ + 2) / 2) / Real.Gamma (Real.pi / θ + 1)) *
      (∫ z : sphere (0 : ℂ) 1, wedgeArcMode θ z ∂((volume : Measure ℂ).toSphere.restrict
        {z : sphere (0 : ℂ) 1 | Complex.arg z ∈ Ioo (-θ / 2) (θ / 2)})) *
      (2 * t) ^ (-(Real.pi / θ) / 2) *
      (Real.sqrt (2 / θ) * wedgeAngularMode θ 0) =
    (4 / Real.pi) *
      (Real.Gamma ((Real.pi / θ + 2) / 2) / Real.Gamma (Real.pi / θ + 1)) *
      (2 * t) ^ (-(Real.pi / θ) / 2) := by
  have h := wedge_first_mode_axis_factor hθ hθ'
  calc
    _ = ((∫ z : sphere (0 : ℂ) 1, wedgeArcMode θ z ∂((volume : Measure ℂ).toSphere.restrict
      {z : sphere (0 : ℂ) 1 | Complex.arg z ∈ Ioo (-θ / 2) (θ / 2)})) *
      (Real.sqrt (2 / θ) * wedgeAngularMode θ 0)) *
      (Real.Gamma ((Real.pi / θ + 2) / 2) / Real.Gamma (Real.pi / θ + 1)) *
      (2 * t) ^ (-(Real.pi / θ) / 2) := by ring
    _ = _ := by rw [h]

/-- The resulting first-mode coefficient is positive at every positive time. -/
theorem wedge_first_mode_coefficient_pos {θ t : ℝ} (hθ : 0 < θ) (ht : 0 < t) :
    0 < (4 / Real.pi) *
      (Real.Gamma ((Real.pi / θ + 2) / 2) / Real.Gamma (Real.pi / θ + 1)) *
      (2 * t) ^ (-(Real.pi / θ) / 2) := by
  have hp : 0 < Real.pi / θ := div_pos Real.pi_pos hθ
  exact mul_pos (mul_pos (div_pos (by norm_num) Real.pi_pos)
    (div_pos (Real.Gamma_pos_of_pos (by linarith))
      (Real.Gamma_pos_of_pos (by linarith)))) (Real.rpow_pos_of_pos (by positivity) _)

end LatticeProb
