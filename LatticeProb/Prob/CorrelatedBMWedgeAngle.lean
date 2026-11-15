import Mathlib

/-! # The angle of a symmetric correlated Brownian wedge -/

set_option autoImplicit false

namespace LatticeProb.CorrelatedBM

/-- For a correlation `-cos θ`, the sum and difference whitening coefficients
are the sine and cosine of half the wedge opening angle. -/
theorem symmetric_wedge_coefficients (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    Real.sqrt (2 * (1 - Real.cos θ)) / 2 = Real.sin (θ / 2) ∧
    Real.sqrt (2 * (1 + Real.cos θ)) / 2 = Real.cos (θ / 2) := by
  have hs : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have he : 2 * (θ / 2) = θ := by ring
  have hsin : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    simpa only [he] using (Real.cos_two_mul_eq_one_sub (θ / 2))
  have hcos : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    simpa only [he] using (Real.cos_two_mul (θ / 2))
  constructor
  · have hroot : Real.sqrt (2 * (1 - Real.cos θ)) = 2 * Real.sin (θ / 2) := by
      apply (Real.sqrt_eq_iff_eq_sq (by nlinarith [sq_nonneg (Real.sin (θ / 2))])
        (by positivity)).2
      nlinarith
    rw [hroot]
    ring
  · have hroot : Real.sqrt (2 * (1 + Real.cos θ)) = 2 * Real.cos (θ / 2) := by
      apply (Real.sqrt_eq_iff_eq_sq (by nlinarith [sq_nonneg (Real.cos (θ / 2))])
        (by positivity)).2
      nlinarith
    rw [hroot]
    ring

/-- The two unit boundary rays of the symmetric wedge have scalar product
`cos θ`. -/
theorem symmetric_wedge_boundary_dot (θ : ℝ) :
    Real.cos (θ / 2) * Real.cos (θ / 2) +
      Real.sin (θ / 2) * (-Real.sin (θ / 2)) = Real.cos θ := by
  have h := Real.cos_two_mul' (θ / 2)
  have he : 2 * (θ / 2) = θ := by ring
  rw [he] at h
  nlinarith [h]

/-- The mating correlation angle lies strictly between zero and π. -/
theorem mating_angle_bounds (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    0 < Real.pi * γ ^ 2 / 4 ∧ Real.pi * γ ^ 2 / 4 < Real.pi := by
  constructor
  · positivity
  · have hγ4 : γ ^ 2 < 4 := by nlinarith [mul_pos hγ0 (sub_pos.2 hγ2)]
    nlinarith [mul_pos Real.pi_pos (sub_pos.2 hγ4)]

/-- The corresponding wedge exponent is `4 / γ²`. -/
theorem mating_angle_exponent (γ : ℝ) (hγ : γ ≠ 0) :
    Real.pi / (Real.pi * γ ^ 2 / 4) = 4 / γ ^ 2 := by
  field_simp

end LatticeProb.CorrelatedBM
