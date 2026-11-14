/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatScaledAnnulusNesting at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatAnnulusNesting

 

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_scaled_annulus_nested_cross_le
    (ξ : ℝ) (f : ℂ → ℝ) (z : ℂ) (d r : ℝ)
    (hd : 0 < d) (hr1 : 1 ≤ r) (hr2 : r ≤ 2) :
    crossLenIn ξ f (closedBall z ((3 * d / 4) / r))
      (sphere z ((d / 4) / r)) (sphere z ((d / 2) / r)) ≤
      crossLenIn ξ f (closedBall z d)
        (sphere z (d / 16)) (sphere z (3 * d / 4)) := by
  have hr : 0 < r := by linarith
  apply dg20_nested_annulus_cross_le ξ f z (closedBall z d)
    (d / 16) ((d / 4) / r) ((d / 2) / r) (3 * d / 4)
    ((3 * d / 4) / r)
  · have hle : d / 8 ≤ (d / 4) / r := by
      apply (le_div_iff₀ hr).2
      nlinarith [mul_le_mul_of_nonneg_left hr2 hd.le]
    linarith
  · exact div_lt_div_of_pos_right (by linarith) hr
  · have hle : (d / 2) / r ≤ d / 2 := div_le_self (by linarith) hr1
    linarith
  · exact div_le_div_of_nonneg_right (by linarith [hd]) hr.le

end SupercriticalLQGUniqueness.B2.DG20Pt
