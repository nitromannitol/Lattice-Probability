import Mathlib

/-!
# A logarithmic weight on a shell

If `t ≤ ‖w‖ ≤ 3 t` and `ξ ≥ 0`, then `ξ (-α log ‖w‖) ≤ -α ξ log t + |α| ξ log 3`.
-/

noncomputable section

namespace LatticeProb.LQG

/-- On the shell `t ≤ ‖w‖ ≤ 3 t`, the weight `ξ (-α log ‖w‖)` is at most
`-α ξ log t + |α| ξ log 3`. -/
theorem mul_neg_mul_log_norm_le_of_mem_shell {α ξ t : ℝ} (hξ : 0 ≤ ξ) (ht : 0 < t) {w : ℂ}
    (h1 : t ≤ ‖w‖) (h2 : ‖w‖ ≤ 3 * t) :
    ξ * (-α * Real.log ‖w‖) ≤ -α * ξ * Real.log t + |α| * ξ * Real.log 3 := by
  have hw : 0 < ‖w‖ := lt_of_lt_of_le ht h1
  have hl1 : Real.log t ≤ Real.log ‖w‖ := Real.log_le_log ht h1
  have hl2 : Real.log ‖w‖ ≤ Real.log 3 + Real.log t := by
    rw [← Real.log_mul (by norm_num) ht.ne']
    exact Real.log_le_log hw h2
  have hd : (-α) * (Real.log ‖w‖ - Real.log t) ≤ |α| * Real.log 3 :=
    calc (-α) * (Real.log ‖w‖ - Real.log t) ≤ |α| * (Real.log ‖w‖ - Real.log t) :=
          mul_le_mul_of_nonneg_right (neg_le_abs α) (by linarith)
      _ ≤ |α| * Real.log 3 := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg α)
  have := mul_le_mul_of_nonneg_left hd hξ
  nlinarith [this]

end LatticeProb.LQG
