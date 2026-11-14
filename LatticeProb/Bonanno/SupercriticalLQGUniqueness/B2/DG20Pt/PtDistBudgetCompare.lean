/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistBudgetCompare at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistFieldFactor

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_cross_budget_compare (ξ Q T ζ lam u v : ℝ) (k : ℕ)
    (hξ : 0 < ξ) (hT : 0 < T) (hζ : 0 ≤ ζ) (hlam : 0 ≤ lam)
    (hfield : |u - v| ≤ (Real.log T + ζ * (k : ℝ)) / ξ) :
    Real.exp (ξ * u) *
      (T * ((2 : ℝ) ^ (-(ξ * Q - ζ) * (k : ℝ)) * lam)) ≤
      T ^ 2 * (2 : ℝ) ^ (-(ξ * Q - 3 * ζ) * (k : ℝ)) *
        Real.exp (ξ * v) * lam := by
  have h := pt_dist_site_cost_compare ξ Q T ζ u v k hξ hT hζ hfield
  have h' := mul_le_mul_of_nonneg_right h hlam
  simpa only [mul_assoc] using h'

theorem pt_dist_loop_budget_compare (ξ Q T ζ C lam u v : ℝ) (k : ℕ)
    (hξ : 0 < ξ) (hT : 0 < T) (hζ : 0 ≤ ζ)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hfield : |u - v| ≤ (Real.log T + ζ * (k : ℝ)) / ξ) :
    T * (C * (2 : ℝ) ^ (-(ξ * Q - ζ) * (k : ℝ)) * lam) *
      Real.exp (ξ * u) ≤
      C * T ^ 2 * (2 : ℝ) ^ (-(ξ * Q - 3 * ζ) * (k : ℝ)) *
        Real.exp (ξ * v) * lam := by
  have h := pt_dist_site_cost_compare ξ Q T ζ u v k hξ hT hζ hfield
  have h' := mul_le_mul_of_nonneg_right h (mul_nonneg hC hlam)
  calc
    _ = (Real.exp (ξ * u) *
      (T * (2 : ℝ) ^ (-(ξ * Q - ζ) * (k : ℝ)))) * (C * lam) := by ring
    _ ≤ (T ^ 2 * (2 : ℝ) ^ (-(ξ * Q - 3 * ζ) * (k : ℝ)) *
      Real.exp (ξ * v)) * (C * lam) := h'
    _ = _ := by ring

end SupercriticalLQGUniqueness.B2.DG20Pt
