/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistPointGaussianRate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistPointGaussianEvent

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_point_gaussian_rate_linear
    (ξ L β : ℝ) (k : ℕ) (hξ : 0 < ξ) (hL : 0 ≤ L)
    (hβ : 0 < β) (hk : 0 < k) :
    (β / (2 * ξ ^ 2 * Real.log 2)) *
      (L + β * (k : ℝ)) ≤
      ((L + β * (k : ℝ)) / ξ) ^ 2 /
        (2 * ((k : ℝ) * Real.log 2)) := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hterm : 0 ≤ L + β * (k : ℝ) := by positivity
  have hbase : β * (k : ℝ) * (L + β * (k : ℝ)) ≤
      (L + β * (k : ℝ)) ^ 2 := by
    nlinarith [mul_nonneg hL hterm]
  have hden : 0 < 2 * ξ ^ 2 * (k : ℝ) * Real.log 2 := by positivity
  have hdiv := div_le_div_of_nonneg_right hbase hden.le
  calc
    _ = (β * (k : ℝ) * (L + β * (k : ℝ))) /
        (2 * ξ ^ 2 * (k : ℝ) * Real.log 2) := by
          field_simp
    _ ≤ (L + β * (k : ℝ)) ^ 2 /
        (2 * ξ ^ 2 * (k : ℝ) * Real.log 2) := hdiv
    _ = _ := by
      field_simp

end SupercriticalLQGUniqueness.B2.DG20Pt
