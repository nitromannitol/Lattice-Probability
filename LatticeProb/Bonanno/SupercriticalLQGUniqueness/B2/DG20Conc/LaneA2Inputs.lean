/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Inputs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRepairedInputs

 





set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SupercriticalLQGUniqueness.B2.DG20Conc.LaneBInputs

 


def C1UnitBlockGeometry : Prop :=
  LaneCRepairedInputs.UnitBlockGeometry
    laneCUnitUcross laneCUnitUaround laneCUnitInner laneCUnitOuter

end SupercriticalLQGUniqueness.B2.DG20Conc.LaneBInputs
