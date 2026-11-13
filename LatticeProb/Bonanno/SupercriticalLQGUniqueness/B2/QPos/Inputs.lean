/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.Inputs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements

 





set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.QPos.Inputs

 



def WhiteNoiseMedianPowerWindow : Prop :=
  ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
      ∀ δ : ℝ, 0 < δ →
        ∀ᶠ n : ℕ in atTop,
          (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + δ) * (n : ℝ)) ≤
            lambdaN (ξ : ℝ) W P n ∧
          lambdaN (ξ : ℝ) W P n ≤
            (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - δ) * (n : ℝ))

end SupercriticalLQGUniqueness.B2.QPos.Inputs
