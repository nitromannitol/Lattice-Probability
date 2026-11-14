/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Rate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2BridgeThreshold
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneAShift

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneA2_sqrt_shifted_log_rate {S T : ℝ}
    (hS : 6 < S) (hSsq : S ^ 2 = T)
    (hlog : Real.log S = Real.log T / 2) :
    (Real.log T)^2 / (16 * Real.log (Real.log T)) ≤
      (Real.log (S / 2))^2 / Real.log (Real.log (S / 2)) := by
  have hbase := laneA_shifted_log_rate (G := 2) (T := S)
    (by norm_num : (1 : ℝ) ≤ 2)
    (by norm_num at hS ⊢; linarith)
  have hT0 : 0 < T := by rw [← hSsq]; positivity
  have hST : S ≤ T := by rw [← hSsq]; nlinarith
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hllS : 0 < Real.log (Real.log S) := by
    apply Real.log_pos
    have hlog3 : 1 < Real.log 3 := by linarith [Real.log_three_gt_d9]
    exact hlog3.trans (Real.log_lt_log (by norm_num) (by linarith))
  have hllT : 0 < Real.log (Real.log T) := by
    apply Real.log_pos
    have hlog3 : 1 < Real.log 3 := by linarith [Real.log_three_gt_d9]
    exact hlog3.trans (Real.log_lt_log (by norm_num) (by linarith))
  have hll : Real.log (Real.log S) ≤ Real.log (Real.log T) :=
    Real.log_le_log hlogS
      (Real.log_le_log (by linarith) hST)
  calc
    (Real.log T)^2 / (16 * Real.log (Real.log T)) =
        (Real.log S)^2 / (4 * Real.log (Real.log T)) := by rw [hlog]; ring
    _ ≤ (Real.log S)^2 / (4 * Real.log (Real.log S)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _)
      · positivity
      · exact mul_le_mul_of_nonneg_left hll (by norm_num)
    _ ≤ (Real.log (S / 2))^2 / Real.log (Real.log (S / 2)) := by
      convert hbase using 1 <;> norm_num

end SupercriticalLQGUniqueness.B2.DG20Conc
