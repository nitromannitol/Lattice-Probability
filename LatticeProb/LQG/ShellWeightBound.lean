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

/-- **Shell weights against a linear drift.** For `ξ ≥ 0`, `s > 0` and `α ≤ α'` with `α' ≥ 0`
there is a constant `c₀` such that for all `k`, with `ℓ = log (s / 2 ^ (k + 1))`,
`max 0 (-α ξ ℓ + |α| ξ log 3) + (-(η k) + ξ α' ℓ) + ε k ≤ c₀ - (η - ε) k`. -/
theorem eventually_shellWeight_add_le {α α' ξ η ε s : ℝ} (hξ : 0 ≤ ξ) (hs : 0 < s)
    (hα : α ≤ α') (hα' : 0 ≤ α') :
    ∃ c₀ : ℝ, ∀ k : ℕ, max 0 (-α * ξ * Real.log (s / 2 ^ (k + 1)) + |α| * ξ * Real.log 3) +
      (-(η * k) + ξ * α' * Real.log (s / 2 ^ (k + 1))) + ε * k ≤ c₀ - (η - ε) * k := by
  refine ⟨max (ξ * α' * Real.log s) (ξ * (α' - α) * Real.log s + |α| * ξ * Real.log 3),
    fun k => ?_⟩
  have h2k : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  have hl : Real.log (s / 2 ^ (k + 1)) ≤ Real.log s :=
    Real.log_le_log (div_pos hs h2k) (div_le_self hs.le (one_le_pow₀ one_le_two))
  have h1 : 0 ≤ ξ * α' := mul_nonneg hξ hα'
  have h2 : 0 ≤ ξ * (α' - α) := mul_nonneg hξ (sub_nonneg.2 hα)
  have hm1 := le_max_left (ξ * α' * Real.log s) (ξ * (α' - α) * Real.log s + |α| * ξ * Real.log 3)
  have hm2 := le_max_right (ξ * α' * Real.log s)
    (ξ * (α' - α) * Real.log s + |α| * ξ * Real.log 3)
  have e1 := mul_le_mul_of_nonneg_left hl h1
  have e2 := mul_le_mul_of_nonneg_left hl h2
  rcases le_total 0 (-α * ξ * Real.log (s / 2 ^ (k + 1)) + |α| * ξ * Real.log 3) with h | h
  · rw [max_eq_right h]
    nlinarith [e2, hm2]
  · rw [max_eq_left h]
    nlinarith [e1, hm1]

end LatticeProb.LQG
