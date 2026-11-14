/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RFinal at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RClosure
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.QPosClosure
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.ExistsUnique_isLFPPExponent

 









set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 
theorem laneA4ExponentExists_proved : LaneA4ExponentExists :=
  fun ξ => (existsUnique_isLFPPExponent ξ).exists

 
theorem laneA4_efronFactors_of_laneC (hC2 : LaneC2StarAt.{0})
    (hInd : LaneFineStarIndepCoarse.{0}) :
    ∀ ξ : Ioi (0 : ℝ), ∃ Qψ : PsiParams, PsiSmall Qψ ∧ ∃ p : ℝ, 0 < p ∧ p < 2⁻¹ ∧
      J2Inputs.EfronFactors ξ Qψ p :=
  laneA4_efronFactors_of_inputs hC2 hInd laneA4ExponentExists_proved
    QPos.dg20ExponentPositive_proved

theorem laneA4_dg20QuantileRatio_of_laneC (hC2 : LaneC2StarAt.{0})
    (hInd : LaneFineStarIndepCoarse.{0}) : Iface.DG20QuantileRatio :=
  laneA4_dg20QuantileRatio_of_inputs hC2 hInd laneA4ExponentExists_proved
    QPos.dg20ExponentPositive_proved

theorem laneA4_dg20ExponentRelation_of_laneC (hC2 : LaneC2StarAt.{0})
    (hInd : LaneFineStarIndepCoarse.{0}) : Iface.DG20ExponentRelation :=
  laneA4_dg20ExponentRelation_of_inputs hC2 hInd laneA4ExponentExists_proved
    QPos.dg20ExponentPositive_proved

theorem laneA4_dg20PercEstimate_of_laneC (hC2 : LaneC2StarAt.{0})
    (hInd : LaneFineStarIndepCoarse.{0}) : Iface.DG20PercEstimate' :=
  laneA4_dg20PercEstimate_of_inputs hC2 hInd laneA4ExponentExists_proved
    QPos.dg20ExponentPositive_proved

end SupercriticalLQGUniqueness.B2.DG20Conc
