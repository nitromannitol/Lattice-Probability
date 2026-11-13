/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P9JointClosure at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.InputsJoint
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.VaryingJointTransfer
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P9DGFFClosure
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.Uniqueness

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.QPos

 

theorem dgff_upper_window_of_jointComparison
    (hjoint : Inputs.DGFFWhiteNoiseJointComparison)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => boxDGFF n
      {h | dgffAnnulusDistance n (ξ : ℝ) h ≤
        (2 : ℝ) ^ (((ξ : ℝ) * Q + ε) * (n : ℝ))})
      atTop (𝓝 1) := by
  obtain ⟨W, hW⟩ := LQGMetric.WhiteNoise.exists_isWhiteNoise
  let P := LQGDimension.ExistAsm.stdP
  obtain ⟨J, hJprob, hJD, hJP, hJevent⟩ := hjoint ξ P W hW
  letI (n : ℕ) : IsProbabilityMeasure (J n) := hJprob n
  let Y : ℕ → _ → ℝ := fun n ω =>
    (crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
      upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal
  have hY : ∀ n, Measurable (Y n) := by
    intro n
    have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
    exact (measurable_crossLenIn upperAnnulus_isCompact hφ.cont hφ.meas).ennreal_toReal
  have hwhite : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => P {ω | Y n ω ≤
        (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - δ) * (n : ℝ))})
        atTop (𝓝 1) := by
    intro δ hδ
    exact upper_annulus_power_window_proved hW ξ Q hQ hδ
  exact varying_joint_comparison_upper_window
    (fun n => boxDGFF n) P J
    (fun n => dgffAnnulusDistance n (ξ : ℝ)) Y
    (fun n => measurable_dgffAnnulusDistance n (ξ : ℝ)) hY
    hJD hJP (ξ : ℝ) Q hwhite hJevent ε hε

 

theorem dg20ExponentPositive_of_P5_jointComparison
    (hlower : Inputs.DGFFInductionLowerWindow)
    (hjoint : Inputs.DGFFWhiteNoiseJointComparison) :
    Iface.DG20ExponentPositive := by
  intro ξ Q hQ
  exact dgff_exponent_positive_of_upper_window hlower ξ Q
    (fun ε hε => dgff_upper_window_of_jointComparison hjoint ξ Q hQ ε hε)

end SupercriticalLQGUniqueness.B2.QPos
