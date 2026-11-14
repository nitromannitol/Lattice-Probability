/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeLongRects at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeAround

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

 
def laneCPrimeLongRect (side : Fin 4) (i : Fin 5) : MarkedRect :=
  let t : ℝ := -3 / 16 + (i.val : ℝ) / 4
  match side.val with
  | 0 => ⟨t, 17 / 16, 3 / 8, 1 / 8, true⟩
  | 1 => ⟨t, -3 / 16, 3 / 8, 1 / 8, true⟩
  | 2 => ⟨-3 / 16, t, 1 / 8, 3 / 8, false⟩
  | _ => ⟨17 / 16, t, 1 / 8, 3 / 8, false⟩

 
def laneCPrimeJoinRect (side : Fin 4) (i : Fin 4) : MarkedRect :=
  let t : ℝ := -3 / 16 + ((i.val : ℝ) + 1) / 4
  match side.val with
  | 0 => ⟨t, 1, 1 / 8, 3 / 8, false⟩
  | 1 => ⟨t, -1 / 4, 1 / 8, 3 / 8, false⟩
  | 2 => ⟨-1 / 4, t, 3 / 8, 1 / 8, true⟩
  | _ => ⟨1, t, 3 / 8, 1 / 8, true⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
