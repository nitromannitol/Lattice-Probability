/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistChainTriangle at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistFiniteChain
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistCollar

 

set_option autoImplicit false
noncomputable section

open LQGMetric LQGMetric.LFPP
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_le_chain_sum
    (ξ : ℝ) (φ : ℂ → ℝ) (U : Set ℂ) (p : ℕ → ℂ) (N : ℕ) :
    lfppDOn ξ φ U (p 0) (p (N + 1)) ≤
      ∑ j ∈ Finset.range (N + 1), lfppDOn ξ φ U (p j) (p (j + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have htri := lfppDOn_triangle (ξ := ξ) (φ := φ) (S := U)
        (p 0) (p (N + 1)) (p (N + 2))
      calc
        lfppDOn ξ φ U (p 0) (p (N + 1 + 1))
            ≤ lfppDOn ξ φ U (p 0) (p (N + 1)) +
              lfppDOn ξ φ U (p (N + 1)) (p (N + 2)) := by simpa only [Nat.add_assoc] using htri
        _ ≤ (∑ j ∈ Finset.range (N + 1), lfppDOn ξ φ U (p j) (p (j + 1))) +
              lfppDOn ξ φ U (p (N + 1)) (p (N + 2)) := add_le_add ih le_rfl
        _ = ∑ j ∈ Finset.range (N + 1 + 1),
              lfppDOn ξ φ U (p j) (p (j + 1)) := by simp only [Finset.sum_range_succ]

end SupercriticalLQGUniqueness.B2.DG20Pt
