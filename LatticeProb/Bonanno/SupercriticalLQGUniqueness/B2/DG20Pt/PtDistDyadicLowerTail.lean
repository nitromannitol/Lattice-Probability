/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistDyadicLowerTail at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistGaussianDecay

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_univ_le_internal
    (ξ : ℝ) (φ : ℂ → ℝ) (U : Set ℂ) (z w : ℂ) :
    lfppDOn ξ φ univ z w ≤ lfppDOn ξ φ U z w := by
  refine le_iInf fun P => ?_
  exact iInf_le_of_le
    ⟨P.1, P.2.1, fun _ _ => mem_univ _⟩ le_rfl

end SupercriticalLQGUniqueness.B2.DG20Pt
