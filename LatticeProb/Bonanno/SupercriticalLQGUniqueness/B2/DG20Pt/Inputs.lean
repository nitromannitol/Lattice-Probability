/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.Inputs at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements
import LatticeProb.Bonanno.LQGMetric.LFPP.PathOps
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 







def DG20ExponentRelation : Prop :=
  ∀ ξ : Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
    ∀ ζ : ℝ, 0 < ζ → ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n →
          C⁻¹ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (k : ℝ)) *
              lambdaN (ξ : ℝ) W P (n - k) ≤ lambdaN (ξ : ℝ) W P n ∧
          lambdaN (ξ : ℝ) W P n ≤
            C * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (k : ℝ)) *
              lambdaN (ξ : ℝ) W P (n - k)

 



namespace Inputs

 


def annulus48 (x : ℂ) (r : ℝ) (hr : 0 < r) : EuclideanAnnulus :=
  ⟨(x, (4 * r, 8 * r)), by constructor <;> linarith⟩

 

def HasAroundLoop (ξ : ℝ) (φ : ℂ → ℝ) (x : ℂ)
    (r : ℝ) (hr : 0 < r) (L : ℝ≥0∞) : Prop :=
  ∃ (γ : ℝ → ℂ) (a b : ℂ),
    LQGMetric.IsPiecewiseC1Path γ a b ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ (annulus48 x r hr).toSet) ∧
    LQGMetric.Disconnects (γ '' Set.Icc (0 : ℝ) 1)
      (annulus48 x r hr).innerBoundary
      (annulus48 x r hr).outerBoundary ∧
    LQGMetric.lfppLen ξ φ γ < L

 





def DG20AroundEstimate : Prop :=
  ∀ ξ : Ioi (0 : ℝ),
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
        (_hW : IsWhiteNoise P W),
        ∀ n k : ℕ, k ≤ n → ∀ x : ℂ, ∀ T : ℝ, 3 < T →
          let r : ℝ := ((2 : ℝ)⁻¹) ^ k
          P {ω | ¬ HasAroundLoop (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
                x r (by dsimp [r]; positivity)
                (ENNReal.ofReal (T * r * lambdaN (ξ : ℝ) W P (n - k) *
                  Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω)))} ≤
            ENNReal.ofReal (c₀ * Real.exp
              (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T)))

end Inputs

end SupercriticalLQGUniqueness.B2.DG20Pt
