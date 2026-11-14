/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatScaledAnnulusCost at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaledAnnulusCost

 

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_scaled_annulus_cross_compare
    (ξ : ℝ) (F g : ℂ → ℝ) (z : ℂ) (d r C : ℝ)
    (hr : 0 < r) (hr2 : r ≤ 2) (hC : 0 ≤ C)
    (hfieldCross :
      crossLenIn ξ (fun x => g ((r : ℂ) * x))
        (closedBall z ((3 * d / 4) / r))
        (sphere z ((d / 4) / r)) (sphere z ((d / 2) / r)) ≤
      ENNReal.ofReal C * crossLenIn ξ F
        (closedBall z ((3 * d / 4) / r))
        (sphere z ((d / 4) / r)) (sphere z ((d / 2) / r))) :
    crossLenIn ξ g
        (closedBall ((r : ℂ) * z) (3 * d / 4))
        (sphere ((r : ℂ) * z) (d / 4))
        (sphere ((r : ℂ) * z) (d / 2)) ≤
      ENNReal.ofReal (2 * C) * crossLenIn ξ F
        (closedBall z ((3 * d / 4) / r))
        (sphere z ((d / 4) / r)) (sphere z ((d / 2) / r)) := by
  have hscale := pt_dist_scaled_annulus_cross_cost ξ g z d r hr
  have hrTwo : ENNReal.ofReal r ≤ (2 : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal hr2
  have hprod : (2 : ℝ≥0∞) * ENNReal.ofReal C =
      ENNReal.ofReal (2 * C) := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
  calc
    crossLenIn ξ g
        (closedBall ((r : ℂ) * z) (3 * d / 4))
        (sphere ((r : ℂ) * z) (d / 4))
        (sphere ((r : ℂ) * z) (d / 2)) =
      ENNReal.ofReal r * crossLenIn ξ (fun x => g ((r : ℂ) * x))
        (closedBall z ((3 * d / 4) / r))
        (sphere z ((d / 4) / r)) (sphere z ((d / 2) / r)) := hscale.symm
    _ ≤ 2 * crossLenIn ξ (fun x => g ((r : ℂ) * x))
        (closedBall z ((3 * d / 4) / r))
        (sphere z ((d / 4) / r)) (sphere z ((d / 2) / r)) := by gcongr
    _ ≤ 2 * (ENNReal.ofReal C * crossLenIn ξ F
        (closedBall z ((3 * d / 4) / r))
        (sphere z ((d / 4) / r)) (sphere z ((d / 2) / r))) := by gcongr
    _ = ENNReal.ofReal (2 * C) * crossLenIn ξ F
        (closedBall z ((3 * d / 4) / r))
        (sphere z ((d / 4) / r)) (sphere z ((d / 2) / r)) := by
      rw [← hprod]
      ac_rfl

end SupercriticalLQGUniqueness.B2.DG20Pt
