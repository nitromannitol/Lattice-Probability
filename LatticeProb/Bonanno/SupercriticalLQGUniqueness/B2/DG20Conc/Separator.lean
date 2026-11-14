/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.Separator at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.ConnectedDomain
import LatticeProb.Bonanno.LQGMetric.LFPP.PathAnalytic
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Geom

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem exists_positive_infDist_gap
    {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAn : A.Nonempty) (hAB : Disjoint A B) :
    ∃ d : ℝ, 0 < d ∧ ∀ b ∈ B, d ≤ infDist b A := by
  have hpos : ∀ b ∈ B, 0 < infDist b A := by
    intro b hb
    have hbA : b ∉ A := fun hba => (disjoint_left.mp hAB) hba hb
    exact (hA.isClosed.notMem_iff_infDist_pos hAn).mp hbA
  exact hB.exists_forall_le' (continuous_infDist_pt A).continuousOn hpos

 
end SupercriticalLQGUniqueness.B2.DG20Conc
