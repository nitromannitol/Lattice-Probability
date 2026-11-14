/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistChain at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAroundBridge

 


set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_chain_edges {ξ : ℝ} {f : ℂ → ℝ} {U : Set ℂ}
    (v : ℕ → ℂ) (a : ℕ → ℝ≥0∞) (N : ℕ) (hv : v 0 ∈ U)
    (hstep : ∀ j < N, lfppDOn ξ f U (v j) (v (j + 1)) ≤ a j) :
    lfppDOn ξ f U (v 0) (v N) ≤ ∑ j ∈ Finset.range N, a j := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact (lfppDOn_le (isPiecewiseC1Path_const (v 0))
      (fun _ _ => hv)).trans (by rw [lfppLen_const])
  | succ N ih =>
    rw [Finset.sum_range_succ]
    exact (lfppDOn_triangle _ (v N) _).trans
      (add_le_add (ih fun j hj => hstep j (by omega)) (hstep N (by omega)))

 

end SupercriticalLQGUniqueness.B2.DG20Pt
