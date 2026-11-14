/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2UnitLong at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Tails
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Union

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

theorem laneA2_unit_long_tail
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {ξ p Cneg cNeg Cpos cPos : ℝ}
    (hunit : LaneA2UnitTails.{u} ξ p Cneg cNeg Cpos cPos)
    (m : ℕ) (T : ℝ) (hT : 3 < T) (u : Circle) (c : ℂ) :
    P {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
        ellN ξ W P m (ENNReal.ofReal p) <
        T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω) 0 u c 3 1} ≤
      ENNReal.ofReal (Cpos * Real.exp
        (-cPos * (Real.log T)^2 / Real.log (Real.log T))) := by
  have h := (hunit P W hW m T hT).2
  have hlaw := T20B.law_mrectLen (ξ := ξ) hW (Nat.zero_le m) u c 3 1
    (S := Set.Ioi (T * LambdaN ξ W P m (ENNReal.ofReal p) *
      ellN ξ W P m (ENNReal.ofReal p))) measurableSet_Ioi
  simp only [pow_zero, one_mul, Nat.sub_zero] at hlaw
  change P {ω | T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω)
      0 u c 3 1 ∈ Set.Ioi (T * LambdaN ξ W P m (ENNReal.ofReal p) *
        ellN ξ W P m (ENNReal.ofReal p))} ≤ _
  rw [hlaw]
  exact h

end SupercriticalLQGUniqueness.B2.DG20Conc
