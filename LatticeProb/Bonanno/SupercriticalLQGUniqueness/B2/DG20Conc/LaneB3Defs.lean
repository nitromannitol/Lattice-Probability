/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3Defs at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenObs
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiField

 











set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3Defs

open LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

 

def B3FixedPSubaddTails (Qψ : PsiParams) (ξ : Ioi (0 : ℝ)) (Q p : ℝ) : Prop :=
  ∀ ζ C : ℝ, 0 < ζ → 0 < C →
    ∃ K₀ : ℕ, ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
      ∀ n K : ℕ, K₀ ≤ K → K ≤ n →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
        ∀ T : ℝ, (2 : ℝ) ^ ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀)) < T →
          P {ω | lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1) ω <
            T⁻¹ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (K : ℝ)) *
              lambdaN (ξ : ℝ) W P (n - K)} ≤
            ENNReal.ofReal (c₀ * (5 : ℝ) ^ K *
              Real.exp (-(c₁ * (Real.log T) ^ 2 /
                ((K : ℝ) ^ (3 * Qψ.ε₀) * Real.log (Real.log T))))) ∧
          P {ω | T * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (K : ℝ)) *
              lambdaN (ξ : ℝ) W P (n - K) <
                lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1) ω} ≤
            ENNReal.ofReal (c₀ * (5 : ℝ) ^ K *
              Real.exp (-(c₁ * (Real.log T) ^ 2 /
                ((K : ℝ) ^ (3 * Qψ.ε₀) * Real.log (Real.log T)))))

 

end SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3Defs
