/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3Log at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P21Ratio
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CDefs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCInputs
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

 







set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneA3_log_resampling_le
    {L Lcopy A : ℝ} (hL : 0 < L) (hLcopy : 0 < Lcopy)
    (hcopy : Lcopy ≤ L + A) :
    Real.log Lcopy - Real.log L ≤ A / L := by
  calc
    Real.log Lcopy - Real.log L = Real.log (Lcopy / L) := by
      rw [Real.log_div hLcopy.ne' hL.ne']
    _ ≤ Lcopy / L - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hLcopy hL)
    _ ≤ A / L := by
      have hfrac : Lcopy / L ≤ 1 + A / L := by
        apply (div_le_iff₀ hL).mpr
        rw [add_mul, one_mul, div_mul_cancel₀ _ hL.ne']
        exact hcopy
      linarith

end SupercriticalLQGUniqueness.B2.DG20Conc
