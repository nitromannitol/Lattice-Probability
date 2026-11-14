/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1UnitCompact at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSmallAnnulusGeometry
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPushBounds

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem j1_unit_cross_isClosed (i : Bool) : IsClosed (laneCUnitUcross i) := by
  cases i
  · exact isClosed_closure
  · exact (isClosed_Icc.reProdIm isClosed_Icc).sdiff isOpen_interior

theorem j1_unit_cross_isCompact (i : Bool) : IsCompact (laneCUnitUcross i) := by
  exact laneC_outer_cluster_compact.of_isClosed_subset
    (j1_unit_cross_isClosed i) (laneB_unit_small_annuli_subset_outer_cluster i)

end SupercriticalLQGUniqueness.B2.DG20Conc
