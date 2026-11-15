import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen4

/-! # Angular Dirichlet mode on an interval -/

set_option autoImplicit false

namespace LatticeProb

/-- The positive sine mode on the symmetric interval of length `θ`. -/
noncomputable def wedgeAngularMode (θ x : ℝ) : ℝ :=
  Real.sin (Real.pi / θ * (x - (-θ / 2)))

/-- The mode vanishes at both endpoints. -/
theorem wedgeAngularMode_endpoints {θ : ℝ} (hθ : 0 < θ) :
    wedgeAngularMode θ (-θ / 2) = 0 ∧ wedgeAngularMode θ (θ / 2) = 0 := by
  constructor
  · simp [wedgeAngularMode]
  · have h : Real.pi / θ * (θ / 2 - (-θ / 2)) = Real.pi := by
      field_simp
      ring
    simp [wedgeAngularMode, h]

/-- The mode is strictly positive between the endpoints. -/
theorem wedgeAngularMode_pos {θ x : ℝ} (hθ : 0 < θ)
    (hx : x ∈ Set.Ioo (-θ / 2) (θ / 2)) : 0 < wedgeAngularMode θ x := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos (div_pos Real.pi_pos hθ) (sub_pos.mpr hx.1)
  · have hstep : x - (-θ / 2) < θ := by linarith [hx.2]
    have hmul := mul_lt_mul_of_pos_left hstep (div_pos Real.pi_pos hθ)
    have heq : Real.pi / θ * θ = Real.pi := by field_simp
    linarith

/-- The mode equals one at the centre. -/
theorem wedgeAngularMode_zero {θ : ℝ} (hθ : 0 < θ) : wedgeAngularMode θ 0 = 1 := by
  have h : Real.pi / θ * (0 - (-θ / 2)) = Real.pi / 2 := by
    field_simp
    ring
  change Real.sin (Real.pi / θ * (0 - (-θ / 2))) = 1
  rw [h, Real.sin_pi_div_two]

/-- The second derivative of the mode equals `-(π / θ)^2` times the mode. -/
theorem hasDerivAt_deriv_wedgeAngularMode (θ x : ℝ) :
    HasDerivAt (deriv (wedgeAngularMode θ))
      (-(Real.pi / θ) ^ 2 * wedgeAngularMode θ x) x := by
  have hderiv : deriv (wedgeAngularMode θ) =
      fun y => Real.pi / θ * Real.cos (Real.pi / θ * (y - (-θ / 2))) := by
    funext y
    exact (LQGMetric.HeatSq.hasDerivAt_sinShift (Real.pi / θ) (-θ / 2) y).deriv
  rw [hderiv]
  exact LQGMetric.HeatSq.hasDerivAt_cosShift (Real.pi / θ) (-θ / 2) x

end LatticeProb
