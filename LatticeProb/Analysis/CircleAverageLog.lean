import Mathlib

/-!
# Logarithmic circle averages

Calculus of the circle average of the logarithm of the norm, `z ↦ Real.circleAverage (fun x ↦ Real.log ‖x‖) z r`:
the scaling law in the centre and the radius (`circleAverage_log_scale`), the value at the origin
(`circleAverage_log_zero`), and the identity `exp (-x) * exp x = 1` (`exp_neg_mul_exp_self`).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb.CircleAverageLog

/-- Scaling of the logarithmic circle average: `cavg(log|·|)(R v, R s) = log R + cavg(log|·|)(v, s)`. -/
theorem circleAverage_log_scale {R s : ℝ} (hR : 0 < R) (hs : 0 < s) (v : ℂ) :
    Real.circleAverage (fun x => Real.log ‖x‖) ((R : ℂ) * v) (R * s)
      = Real.log R + Real.circleAverage (fun x => Real.log ‖x‖) v s := by
  have h1 := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := (R : ℂ) * v)
    (R := R * s) (mul_pos hR hs).ne'
  have h2 := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := v) (R := s)
    hs.ne'
  simp only [sub_zero] at h1 h2
  have hn : (R * s)⁻¹ * ‖(R : ℂ) * v‖ = s⁻¹ * ‖v‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
    field_simp
  rw [h1, h2, hn, Real.log_mul hR.ne' hs.ne']
  ring

/-- The logarithmic circle average at the origin: `cavg(log|·|)(0, R) = log R`. -/
theorem circleAverage_log_zero {R : ℝ} (hR : 0 < R) :
    Real.circleAverage (fun x => Real.log ‖x‖) 0 R = Real.log R := by
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := 0) (R := R) hR.ne'
  simp only [sub_zero, norm_zero, mul_zero, Real.posLog_zero, add_zero] at h
  exact h

/-- For `x : ℝ`, `exp(-x) · exp(x) = 1`. -/
theorem exp_neg_mul_exp_self (x : ℝ) : Real.exp (-x) * Real.exp x = 1 := by
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

end LatticeProb.CircleAverageLog
