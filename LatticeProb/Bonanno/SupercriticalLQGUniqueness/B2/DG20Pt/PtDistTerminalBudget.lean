/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistTerminalBudget at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistDyadicNorm
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistFieldFactor

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_terminal_budget_compare
    (ξ Q ζ C T lam u : ℝ) (n : ℕ)
    (hξ : 0 < ξ) (hζ : 0 ≤ ζ) (hC : 0 < C) (hT : 0 < T)
    (hT1 : 1 ≤ T)
    (hlam : C⁻¹ * (2 : ℝ) ^ (-(1 - ξ * Q + ζ) * (n : ℝ)) ≤ lam) :
    Real.exp (ξ * (u + (Real.log T + ζ * (n : ℝ)) / ξ)) *
      ((2 : ℝ) ^ (-(n : ℝ)) / 2) ≤
      C * T * lam * (2 : ℝ) ^ (-(ξ * Q - 3 * ζ) * (n : ℝ)) *
        Real.exp (ξ * u) := by
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hnum : 0 ≤ Real.log T + ζ * (n : ℝ) := by positivity
  have hthresh : 0 ≤ (Real.log T + ζ * (n : ℝ)) / ξ :=
    div_nonneg hnum hξ.le
  have hfield :
      |(u + (Real.log T + ζ * (n : ℝ)) / ξ) - u| ≤
        (Real.log T + ζ * (n : ℝ)) / ξ := by
    rw [add_sub_cancel_left, abs_of_nonneg hthresh]
  have hcomp := pt_dist_exp_field_compare ξ T ζ
    (u + (Real.log T + ζ * (n : ℝ)) / ξ) u n hξ hT hfield
  have hpow := pt_dist_exp_linear_le_two_rpow_double ζ hζ n
  have hdyad := pt_dist_dyadic_norm_le ξ Q ζ C lam n hC hlam
  have hcombine :
      (2 : ℝ) ^ (2 * ζ * (n : ℝ)) *
        (2 : ℝ) ^ (-(ξ * Q - ζ) * (n : ℝ)) =
      (2 : ℝ) ^ (-(ξ * Q - 3 * ζ) * (n : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hbase : 0 ≤ (2 : ℝ) ^ (-(n : ℝ)) := by positivity
  have hfac : 0 ≤ T * (2 : ℝ) ^ (2 * ζ * (n : ℝ)) *
      Real.exp (ξ * u) := by positivity
  calc
    _ ≤ Real.exp (ξ * (u + (Real.log T + ζ * (n : ℝ)) / ξ)) *
        (2 : ℝ) ^ (-(n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    _ ≤ (T * Real.exp (ζ * (n : ℝ)) * Real.exp (ξ * u)) *
        (2 : ℝ) ^ (-(n : ℝ)) :=
      mul_le_mul_of_nonneg_right hcomp hbase
    _ ≤ (T * (2 : ℝ) ^ (2 * ζ * (n : ℝ)) * Real.exp (ξ * u)) *
        (2 : ℝ) ^ (-(n : ℝ)) := by
      gcongr
    _ ≤ (T * (2 : ℝ) ^ (2 * ζ * (n : ℝ)) * Real.exp (ξ * u)) *
        (C * lam * (2 : ℝ) ^ (-(ξ * Q - ζ) * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hdyad hfac
    _ = C * T * lam *
        ((2 : ℝ) ^ (2 * ζ * (n : ℝ)) *
          (2 : ℝ) ^ (-(ξ * Q - ζ) * (n : ℝ))) *
        Real.exp (ξ * u) := by ring
    _ = _ := by rw [hcombine]

end SupercriticalLQGUniqueness.B2.DG20Pt
