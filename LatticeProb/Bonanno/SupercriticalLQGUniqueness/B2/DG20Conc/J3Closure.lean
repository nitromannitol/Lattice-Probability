/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J3Closure at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J3PercEstimate
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J2Closure

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise J2Inputs

 
theorem j3_dg20PercEstimate_of_efronFactors
    (hJ : ∀ ξ : Set.Ioi (0 : ℝ), ∃ Qψ : PsiParams, PsiSmall Qψ ∧
      ∃ p : ℝ, 0 < p ∧ p < 2⁻¹ ∧ EfronFactors ξ Qψ p) :
    Iface.DG20PercEstimate' :=
  j3_percEstimate_of_quantileRatioAllP (j2_quantileRatioAllP_of_efronFactors hJ)

end SupercriticalLQGUniqueness.B2.DG20Conc

open SupercriticalLQGUniqueness.B2.DG20Conc
