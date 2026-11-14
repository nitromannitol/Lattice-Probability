/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Large at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Inputs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneASource
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBRepairedLargeAnnulusGeometry

 






set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

 

theorem laneA2_cover0_to_old {Ucross Uaround E F : Set ℂ} {N : ℝ}
    (h : LaneCRepairedInputs.RectAnnulusCoverAt Ucross Uaround E F 0 0 N) :
    LaneAInputs.RectAnnulusCover Ucross Uaround E F N := h

 

end SupercriticalLQGUniqueness.B2.DG20Conc
