/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBLogThreshold at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBBoundedCompare

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

 


theorem laneB_cutoff_factor_log_eq (ξ δ T : ℝ) (hT : 0 < T) :
    ENNReal.ofReal (Real.exp (|ξ| * (δ * Real.log T))) =
      ENNReal.ofReal (T ^ (δ * |ξ|)) := by
  congr 1
  rw [Real.rpow_def_of_pos hT]
  congr 1
  ring

 

theorem laneB_cutoff_log_pos (δ T : ℝ) (hδ : 0 < δ) (hT : 1 < T) :
    0 < δ * Real.log T :=
  mul_pos hδ (Real.log_pos hT)

 

end SupercriticalLQGUniqueness.B2.DG20Conc
