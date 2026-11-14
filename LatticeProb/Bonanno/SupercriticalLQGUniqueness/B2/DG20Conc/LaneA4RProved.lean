/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RProved at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RFinal
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RIndep
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RC2Final

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 
theorem laneA4_efronFactors_proved :
    ∀ ξ : Ioi (0 : ℝ), ∃ Qψ : PsiParams, PsiSmall Qψ ∧ ∃ p : ℝ, 0 < p ∧ p < 2⁻¹ ∧
      J2Inputs.EfronFactors ξ Qψ p :=
  laneA4_efronFactors_of_laneC laneC2StarAt_proved.{0} laneFineStar_indep_coarse_proved.{0}

theorem laneA4_dg20QuantileRatio_proved : Iface.DG20QuantileRatio :=
  laneA4_dg20QuantileRatio_of_laneC laneC2StarAt_proved.{0} laneFineStar_indep_coarse_proved.{0}

theorem laneA4_dg20ExponentRelation_proved : Iface.DG20ExponentRelation :=
  laneA4_dg20ExponentRelation_of_laneC laneC2StarAt_proved.{0}
    laneFineStar_indep_coarse_proved.{0}

theorem laneA4_dg20PercEstimate_proved : Iface.DG20PercEstimate' :=
  laneA4_dg20PercEstimate_of_laneC laneC2StarAt_proved.{0} laneFineStar_indep_coarse_proved.{0}

end SupercriticalLQGUniqueness.B2.DG20Conc
