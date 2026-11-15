import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen4

/-! # Classical Dirichlet sine modes on an interval -/

set_option autoImplicit false

namespace LatticeProb

open LQGMetric.HeatSq

/-- A constant multiple of an interval sine mode vanishes at both endpoints. -/
theorem sinMode_const_mul_endpoints (a L c : ℝ) (k : ℕ) (hL : L ≠ 0) :
    c * sinMode a L k a = 0 ∧ c * sinMode a L k (a + L) = 0 := by
  constructor
  · simp [sinMode]
  · have h : Real.pi * (k : ℝ) * (a + L - a) / L = (k : ℝ) * Real.pi := by
      field_simp
      ring
    change c * Real.sin (Real.pi * (k : ℝ) * (a + L - a) / L) = 0
    rw [h, Real.sin_nat_mul_pi, mul_zero]

/-- The derivative of an interval sine mode, including its normalization. -/
theorem hasDerivAt_const_mul_sinMode (a L c : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y => c * sinMode a L k y)
      (c * (Real.pi * k / L * Real.cos (Real.pi * k / L * (x - a)))) x := by
  have h : (fun y => c * sinMode a L k y) =
      fun y => c * Real.sin (Real.pi * k / L * (y - a)) := by
    funext y
    rw [sinMode_eq]
  rw [h]
  exact (hasDerivAt_sinShift (Real.pi * k / L) a x).const_mul c

/-- Every interval sine mode satisfies its classical Dirichlet eigenvalue equation. -/
theorem hasDerivAt_deriv_const_mul_sinMode (a L c : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (deriv (fun y => c * sinMode a L k y))
      (-(Real.pi * k / L) ^ 2 * (c * sinMode a L k x)) x := by
  have h : deriv (fun y => c * sinMode a L k y) =
      fun y => c * (Real.pi * k / L * Real.cos (Real.pi * k / L * (y - a))) := by
    funext y
    exact (hasDerivAt_const_mul_sinMode a L c k y).deriv
  rw [h, sinMode_eq]
  convert (hasDerivAt_cosShift (Real.pi * k / L) a x).const_mul c using 1
  ring

end LatticeProb
