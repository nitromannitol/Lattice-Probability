/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedApprox at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedTail

 


















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP LQGMetric.DFGPS

 

lemma abs_plProf_le (q ε r : ℝ) : |plProf q ε r| ≤ 1 := by
  have h := plProf_mem_Icc q ε r
  rw [abs_le]; constructor <;> linarith [h.1, h.2]

lemma plTestT_apply' (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (z x : ℂ) :
    plTestT q (ε, z) x = plProf q ε ‖x - z‖ * heatKernel (ε ^ 2 / 2) z x := by
  rw [plTestT_of_mem q hε, plTest_apply, plBump_radial, plProf_eq q ε hε, norm_sub_rev]

 
end SupercriticalLQGUniqueness.B2.Polylog
