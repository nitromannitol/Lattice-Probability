/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaleEvent at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistSiteBoost
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistFieldOsc

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

def ptDistOscGood {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (V : Set ℂ) (k : ℕ) (R t : ℝ) : Set Ω :=
  {ω | ∀ z ∈ V, ∀ w ∈ V,
    dist z w ≤ R * ((2 : ℝ) ^ k)⁻¹ →
      |phiMN W P 0 k z ω - phiMN W P 0 k w ω| ≤ R * t}

def ptDistScaleGood {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (ξ : Ioi (0 : ℝ)) (Q ζ C : ℝ) (n k : ℕ)
    (F : Finset ℂ) (V : Set ℂ) (R t T : ℝ) : Set Ω :=
  ptDistAllSitesGood P W ξ Q ζ C n k F T ∩
    ptDistOscGood P W V k R t

 

end SupercriticalLQGUniqueness.B2.DG20Pt
