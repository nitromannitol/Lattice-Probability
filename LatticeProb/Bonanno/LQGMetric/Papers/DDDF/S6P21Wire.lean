/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P21Wire at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P21
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Wire
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DNum
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DDen
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6TailsDec

/-!
# Theorem 20 inputs from DDDF Prop 21 (task P2-DDDF6c)

`S6T20Inputs` (S6Wire) for `ξ = γ/d_γ` from (5.54) (Condition (T) = Prop 21, `s6_conditionT_psiQ₁`),
(5.67) (`dddf_t20_step4_den`) and the circuit gluing `T20CircuitGlue` for `ψ` with the
parameters `psiQ₁` (gives (5.65)–(5.66) via `t20Step4Num_of_glue`); (6.102)/(6.103) for `[0,1]²` from
`S6T20Inputs` (Theorem 20 gives `Λ` bounded).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `S6T20Inputs` from (5.54) and `T20CircuitGlue` for `psiQ₁` -/
theorem s6T20Inputs_of_glue {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hW : IsWhiteNoise P W)
    (h554 : S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P)
    (hG : T20CircuitGlue (xiGamma γ) S6.psiQ₁ W P) : S6T20Inputs (xiGamma γ) W P :=
  ⟨S6.psiQ₁, S6.psiSmall_psiQ₁, by norm_num [S6.psiQ₁], S6.s6_conditionT_psiQ₁ hγ hγ2 hW h554,
    t20Step4Num_of_glue hW _ (xiGamma_pos' hγ) hG, dddf_t20_step4_den hW _ (xiGamma_pos' hγ)⟩

end DDDF
end LQGMetric
