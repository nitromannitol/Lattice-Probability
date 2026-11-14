/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RClosure at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4REfronFactors
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J2Closure
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J3Closure

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem laneA4_dg20QuantileRatio_of_inputs (hC2 : LaneC2StarAt.{0})
    (hInd : LaneFineStarIndepCoarse.{0}) (hEx : LaneA4ExponentExists)
    (hPos : Iface.DG20ExponentPositive) : Iface.DG20QuantileRatio :=
  j2_dg20QuantileRatio_of_efronFactors (laneA4_efronFactors_of_inputs hC2 hInd hEx hPos)

theorem laneA4_dg20ExponentRelation_of_inputs (hC2 : LaneC2StarAt.{0})
    (hInd : LaneFineStarIndepCoarse.{0}) (hEx : LaneA4ExponentExists)
    (hPos : Iface.DG20ExponentPositive) : Iface.DG20ExponentRelation :=
  j2_dg20ExponentRelation_of_efronFactors (laneA4_efronFactors_of_inputs hC2 hInd hEx hPos)

theorem laneA4_dg20PercEstimate_of_inputs (hC2 : LaneC2StarAt.{0})
    (hInd : LaneFineStarIndepCoarse.{0}) (hEx : LaneA4ExponentExists)
    (hPos : Iface.DG20ExponentPositive) : Iface.DG20PercEstimate' :=
  j3_dg20PercEstimate_of_efronFactors (laneA4_efronFactors_of_inputs hC2 hInd hEx hPos)

end SupercriticalLQGUniqueness.B2.DG20Conc
