/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCDoublePrimeLong at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAnnuli
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S1Geom

 









set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

 
def laneCDoublePrimeLongRect (j : Fin 8) : MarkedRect :=
  match j.val with
  | 0 => ⟨-2, 2, 3, 1, true⟩
  | 1 => ⟨0, 2, 3, 1, true⟩
  | 2 => ⟨-2, -2, 3, 1, true⟩
  | 3 => ⟨0, -2, 3, 1, true⟩
  | 4 => ⟨-2, -2, 1, 3, false⟩
  | 5 => ⟨-2, 0, 1, 3, false⟩
  | 6 => ⟨2, -2, 1, 3, false⟩
  | _ => ⟨2, 0, 1, 3, false⟩

 
theorem laneC_double_prime_long_rect_subset (j : Fin 8) :
    (laneCDoublePrimeLongRect j).toSet ⊆ laneCDoublePrimeCross := by
  have hinner : interior laneCInnerCluster =
      Ioo (-1 : ℝ) 2 ×ℂ Ioo (-1 : ℝ) 2 := by
    simp [laneCInnerCluster, Complex.interior_reProdIm, interior_Icc]
  intro z hz
  fin_cases j <;>
    simp only [laneCDoublePrimeLongRect, MarkedRect.toSet, laneCDoublePrimeCross,
      laneCOuterCluster, hinner, Complex.mem_reProdIm, mem_sdiff, mem_Icc,
      mem_Ioo] at hz ⊢ <;>
    rcases hz with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
  all_goals
    constructor
    · exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    · intro h
      rcases h with ⟨⟨_, _⟩, ⟨_, _⟩⟩
      linarith

 


end SupercriticalLQGUniqueness.B2.DG20Conc
