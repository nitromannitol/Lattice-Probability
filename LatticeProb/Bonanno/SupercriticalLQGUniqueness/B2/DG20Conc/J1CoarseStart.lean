/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseStart at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseParameter

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem j1_coarse_parameter_gt_three
    (ξ B T : ℝ) (hB : 0 ≤ B)
    (hT : (3 : ℝ) ^ (1 + |ξ| * B) < T) :
    3 < j1CoarseTailParameter ξ B T := by
  have hD : 0 < 1 + |ξ| * B := by positivity
  have hT0 : 0 < T :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).trans hT
  have hlog := Real.log_lt_log
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _) hT
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 3)] at hlog
  have hlog' : Real.log 3 < Real.log T /
      (1 + |ξ| * B) := (lt_div_iff₀ hD).mpr (by nlinarith)
  have hs : 0 < j1CoarseTailParameter ξ B T :=
    j1_coarse_parameter_pos ξ B T hT0
  exact (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 3) hs).mp
    (by simpa only [j1_coarse_parameter_log ξ B T hB hT0] using hlog')

end SupercriticalLQGUniqueness.B2.DG20Conc
