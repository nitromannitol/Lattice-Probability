/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.PfeLocal.CircleMin at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements
import Mathlib.Topology.Semicontinuity.Basic

 





set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 


theorem setDistance_eq_at_min (D : LSCMetric) {A B : Set ℂ}
    (hA : IsCompact A) (hB : IsCompact B) (hneA : A.Nonempty) (hneB : B.Nonempty) :
    ∃ u ∈ A, ∃ v ∈ B, Iface.setDistance D.1 A B = D.1 (u, v) := by
  obtain ⟨p, hp, hmin⟩ :=
    (D.2.2.lowerSemicontinuousOn (A ×ˢ B)).exists_isMinOn
      (hneA.prod hneB) (hA.prod hB)
  rcases p with ⟨u, v⟩
  obtain ⟨hu, hv⟩ := hp
  refine ⟨u, hu, v, hv, le_antisymm ?_ ?_⟩
  · exact iInf_le_of_le u (iInf_le_of_le hu
      (iInf_le_of_le v (iInf_le _ hv)))
  · refine le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => ?_
    exact isMinOn_iff.mp hmin ⟨x, y⟩ ⟨hx, hy⟩

 

end SupercriticalLQGUniqueness.B2.PfeLocal
