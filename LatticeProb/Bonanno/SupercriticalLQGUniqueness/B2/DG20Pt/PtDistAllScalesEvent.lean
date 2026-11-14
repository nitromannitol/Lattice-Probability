/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAllScalesEvent at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAllScales

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

def ptDistScaleRate (Cnet : ℕ) (a₀ a₁ b₀ b₁ D σ2 ζ T : ℝ)
    (k : ℕ) (t : ℝ) : ℝ≥0∞ :=
  let S := T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ))
  ((Cnet * 4 ^ k : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal (a₀ * Real.exp
        (-a₁ * (Real.log S) ^ 2 / Real.log (Real.log S))) +
       ENNReal.ofReal (b₀ * Real.exp
        (-b₁ * (Real.log S) ^ 2 / Real.log (Real.log S)))) +
    ENNReal.ofReal (D * 4 ^ k * Real.exp (-t ^ 2 / (2 * σ2)))

 


end SupercriticalLQGUniqueness.B2.DG20Pt
