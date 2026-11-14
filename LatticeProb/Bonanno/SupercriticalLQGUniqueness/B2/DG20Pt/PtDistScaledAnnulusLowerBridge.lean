/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaledAnnulusLowerBridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaledAnnulusCost
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLowerMulArithmetic

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_scaled_annulus_cross_le_point
    (ξ : ℝ) (F g : ℂ → ℝ) (z w : ℂ) (hzw : z ≠ w)
    (r C : ℝ) (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (hC : 0 ≤ C)
    (hfieldCross :
      crossLenIn ξ (fun x => g ((r : ℂ) * x))
        (closedBall z ((3 * dist z w / 4) / r))
        (sphere z ((dist z w / 4) / r))
        (sphere z ((dist z w / 2) / r)) ≤
      ENNReal.ofReal C *
        crossLenIn ξ F
          (closedBall z ((3 * dist z w / 4) / r))
          (sphere z ((dist z w / 4) / r))
          (sphere z ((dist z w / 2) / r))) :
    crossLenIn ξ g
        (closedBall ((r : ℂ) * z) (3 * dist z w / 4))
        (sphere ((r : ℂ) * z) (dist z w / 4))
        (sphere ((r : ℂ) * z) (dist z w / 2)) ≤
      ENNReal.ofReal (2 * C) * lfppDOn ξ F univ z w := by
  let d : ℝ := dist z w
  have hd : 0 < d := dist_pos.mpr hzw
  have hr : 0 < r := lt_of_lt_of_le (by norm_num) hr1
  have ha : 0 < (d / 4) / r := by positivity
  have hab : (d / 4) / r < (d / 2) / r := by
    apply div_lt_div_of_pos_right _ hr
    linarith
  have hbR : (d / 2) / r < (3 * d / 4) / r := by
    apply div_lt_div_of_pos_right _ hr
    linarith
  have hbw : (d / 2) / r < dist z w := by
    have hhalf : (d / 2) / r ≤ d / 2 :=
      div_le_self (by linarith) hr1
    dsimp [d] at hhalf
    linarith
  have hcross :
      crossLenIn ξ F
        (closedBall z ((3 * d / 4) / r))
        (sphere z ((d / 4) / r))
        (sphere z ((d / 2) / r)) ≤
      lfppDOn ξ F univ z w :=
    pt_dist_fixed_annulus_cross_le_point ξ F z w
      ((d / 4) / r) ((d / 2) / r) ((3 * d / 4) / r)
      ha hab hbR hbw
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
      ENNReal.ofReal r *
        crossLenIn ξ (fun x => g ((r : ℂ) * x))
          (closedBall z ((3 * d / 4) / r))
          (sphere z ((d / 4) / r))
          (sphere z ((d / 2) / r)) := hscale.symm
    _ ≤ 2 *
        crossLenIn ξ (fun x => g ((r : ℂ) * x))
          (closedBall z ((3 * d / 4) / r))
          (sphere z ((d / 4) / r))
          (sphere z ((d / 2) / r)) := by gcongr
    _ ≤ 2 * (ENNReal.ofReal C *
        crossLenIn ξ F
          (closedBall z ((3 * d / 4) / r))
          (sphere z ((d / 4) / r))
          (sphere z ((d / 2) / r))) := by gcongr
    _ ≤ ENNReal.ofReal (2 * C) * lfppDOn ξ F univ z w := by
      rw [← hprod]
      calc
        2 * (ENNReal.ofReal C *
          crossLenIn ξ F
            (closedBall z ((3 * d / 4) / r))
            (sphere z ((d / 4) / r))
            (sphere z ((d / 2) / r))) ≤
          2 * (ENNReal.ofReal C * lfppDOn ξ F univ z w) := by gcongr
        _ = (2 * ENNReal.ofReal C) * lfppDOn ξ F univ z w := by ac_rfl

end SupercriticalLQGUniqueness.B2.DG20Pt
