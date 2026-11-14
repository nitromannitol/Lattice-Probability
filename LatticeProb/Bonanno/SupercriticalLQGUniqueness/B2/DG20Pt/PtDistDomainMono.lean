/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistDomainMono at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistBoundedConnectedCore
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistDyadicLowerTail

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_mono_domain
    (ξ : ℝ) (f : ℂ → ℝ) (V U : Set ℂ)
    (hVU : V ⊆ U) (z w : ℂ) :
    lfppDOn ξ f U z w ≤ lfppDOn ξ f V z w := by
  refine le_iInf fun p => ?_
  apply iInf_le_of_le
    (⟨p.1, p.2.1, fun t ht => hVU (p.2.2 t ht)⟩ :
      {p : ℝ → ℂ // IsPiecewiseC1Path p z w ∧
        ∀ t ∈ Icc (0 : ℝ) 1, p t ∈ U})
  exact le_rfl

end SupercriticalLQGUniqueness.B2.DG20Pt
