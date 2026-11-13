/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.UnconditionalP6 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.MedianWindowAdapter
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.UpperPowerWindow
import Mathlib

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.QPos

 
theorem upper_annulus_power_window_proved
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      P {ω | (crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
          upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal ≤
        (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ε) * (n : ℝ))})
      atTop (𝓝 1) :=
  upper_annulus_power_window whiteNoiseMedianPowerWindow_proved hW ξ Q hQ hε

 

end SupercriticalLQGUniqueness.B2.QPos
