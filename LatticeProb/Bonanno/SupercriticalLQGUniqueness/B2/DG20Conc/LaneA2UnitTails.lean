/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2UnitTails at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2CommonP

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

def LaneA2UnitTails (ξ p Cneg cNeg Cpos cPos : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (m : ℕ) (T : ℝ), 3 < T →
    P {ω | lenObs ξ (phiMN W P 0 m) (rectAB 1 3) ω <
      T⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} ≤
      ENNReal.ofReal (Cneg * Real.exp (-cNeg * (Real.log T)^2)) ∧
    P {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
        ellN ξ W P m (ENNReal.ofReal p) <
        lenObs ξ (phiMN W P 0 m) (rectAB 3 1) ω} ≤
      ENNReal.ofReal (Cpos * Real.exp
        (-cPos * (Real.log T)^2 / Real.log (Real.log T)))

def LaneA2HasUnitTails (ξ p : ℝ) : Prop :=
  ∃ Cneg cNeg Cpos cPos : ℝ,
    0 < Cneg ∧ 0 < cNeg ∧ 0 < Cpos ∧ 0 < cPos ∧
    LaneA2UnitTails.{u} ξ p Cneg cNeg Cpos cPos

end SupercriticalLQGUniqueness.B2.DG20Conc
