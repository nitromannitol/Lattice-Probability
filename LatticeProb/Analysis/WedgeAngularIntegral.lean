import LatticeProb.Analysis.WedgeAngularMode
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Integrals of the angular Dirichlet mode -/

set_option autoImplicit false

open MeasureTheory

namespace LatticeProb

/-- The integral of the positive sine mode over the interval. -/
theorem integral_wedgeAngularMode {θ : ℝ} (hθ : 0 < θ) :
    (∫ x in (-θ / 2)..(θ / 2), wedgeAngularMode θ x) = 2 * θ / Real.pi := by
  have hk : Real.pi / θ ≠ 0 := ne_of_gt (div_pos Real.pi_pos hθ)
  have ha : Real.pi / θ * (-θ / 2) + Real.pi / θ * (θ / 2) = 0 := by ring
  have hb : Real.pi / θ * (θ / 2) + Real.pi / θ * (θ / 2) = Real.pi := by
    field_simp
    ring
  have h := intervalIntegral.integral_comp_mul_add Real.sin hk (Real.pi / θ * (θ / 2))
    (a := -θ / 2) (b := θ / 2)
  simp only [ha, hb, smul_eq_mul, integral_sin, Real.cos_zero, Real.cos_pi] at h
  convert h using 1
  · congr 1
    funext x
    simp only [wedgeAngularMode]
    congr 1
    ring
  · field_simp
    ring

/-- The squared integral of the sine mode over the interval. -/
theorem integral_wedgeAngularMode_sq {θ : ℝ} (hθ : 0 < θ) :
    (∫ x in (-θ / 2)..(θ / 2), wedgeAngularMode θ x ^ 2) = θ / 2 := by
  have hk : Real.pi / θ ≠ 0 := ne_of_gt (div_pos Real.pi_pos hθ)
  have ha : Real.pi / θ * (-θ / 2) + Real.pi / θ * (θ / 2) = 0 := by ring
  have hb : Real.pi / θ * (θ / 2) + Real.pi / θ * (θ / 2) = Real.pi := by
    field_simp
    ring
  have h := intervalIntegral.integral_comp_mul_add (fun x => Real.sin x ^ 2) hk
    (Real.pi / θ * (θ / 2)) (a := -θ / 2) (b := θ / 2)
  simp only [ha, hb, smul_eq_mul, integral_sin_sq, Real.sin_zero, Real.sin_pi,
    Real.cos_zero, Real.cos_pi, zero_mul, sub_zero] at h
  convert h using 1
  · congr 1
    funext x
    simp only [wedgeAngularMode]
    congr 2
    ring
  · field_simp
    ring

/-- Scaling the sine mode by `sqrt (2 / θ)` gives unit squared integral. -/
theorem integral_normalized_wedgeAngularMode_sq {θ : ℝ} (hθ : 0 < θ) :
    (∫ x in (-θ / 2)..(θ / 2), (Real.sqrt (2 / θ) * wedgeAngularMode θ x) ^ 2) = 1 := by
  simp only [mul_pow, intervalIntegral.integral_const_mul, integral_wedgeAngularMode_sq hθ,
    Real.sq_sqrt (by positivity : 0 ≤ 2 / θ)]
  field_simp

/-- The integral of the normalized positive sine mode. -/
theorem integral_normalized_wedgeAngularMode {θ : ℝ} (hθ : 0 < θ) :
    (∫ x in (-θ / 2)..(θ / 2), Real.sqrt (2 / θ) * wedgeAngularMode θ x) =
      Real.sqrt (2 / θ) * (2 * θ / Real.pi) := by
  rw [intervalIntegral.integral_const_mul, integral_wedgeAngularMode hθ]

end LatticeProb
