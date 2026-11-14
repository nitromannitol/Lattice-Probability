/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistPointBudget at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistBudgetCompare
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistTerminalBudget

 


set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_selected_budgets_le_point
    (ξ Q ζ C T lam u v : ℝ) (k : ℕ)
    (hξ : 0 < ξ) (hT : 0 < T) (hζ : 0 ≤ ζ)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hfield : |u - v| ≤ (Real.log T + ζ * (k : ℝ)) / ξ) :
    ENNReal.ofReal (2 * (Real.exp (ξ * u) *
      (T * ((2 : ℝ) ^ (-(ξ * Q - ζ) * (k : ℝ)) * lam)))) ≤
      ENNReal.ofReal (2 * T ^ 2 * (2 : ℝ) ^
        (-(ξ * Q - 3 * ζ) * (k : ℝ)) * Real.exp (ξ * v) * lam) ∧
    ENNReal.ofReal (T * (C * (2 : ℝ) ^
      (-(ξ * Q - ζ) * (k : ℝ)) * lam) * Real.exp (ξ * u)) ≤
      ENNReal.ofReal (C * T ^ 2 * (2 : ℝ) ^
        (-(ξ * Q - 3 * ζ) * (k : ℝ)) * Real.exp (ξ * v) * lam) := by
  constructor
  · apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_left
      (pt_dist_cross_budget_compare ξ Q T ζ lam u v k hξ hT hζ hlam hfield)
      (show (0 : ℝ) ≤ 2 by norm_num)
    calc
      _ ≤ 2 * (T ^ 2 * (2 : ℝ) ^ (-(ξ * Q - 3 * ζ) * (k : ℝ)) *
          Real.exp (ξ * v) * lam) := h
      _ = _ := by ring
  · exact ENNReal.ofReal_le_ofReal
      (pt_dist_loop_budget_compare ξ Q T ζ C lam u v k hξ hT hζ hC hlam hfield)

theorem pt_dist_terminal_cost_le_point
    (ξ Q ζ C T lam u : ℝ) (n : ℕ)
    (hξ : 0 < ξ) (hζ : 0 ≤ ζ) (hC : 0 < C)
    (hT : 0 < T) (hT1 : 1 ≤ T)
    (hlam : C⁻¹ * (2 : ℝ) ^ (-(1 - ξ * Q + ζ) * (n : ℝ)) ≤ lam) :
    ENNReal.ofReal (Real.exp (ξ *
      (u + (Real.log T + ζ * (n : ℝ)) / ξ)) *
      (((2 : ℝ)⁻¹ ^ n) / 2)) ≤
    ENNReal.ofReal (C * T * lam * (2 : ℝ) ^
      (-(ξ * Q - 3 * ζ) * (n : ℝ)) * Real.exp (ξ * u)) := by
  apply ENNReal.ofReal_le_ofReal
  simpa only [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast, inv_pow] using
    pt_dist_terminal_budget_compare ξ Q ζ C T lam u n hξ hζ hC hT hT1 hlam

end SupercriticalLQGUniqueness.B2.DG20Pt
