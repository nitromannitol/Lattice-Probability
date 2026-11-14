/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCDoublePrimeWide at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAnnuli
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S1Geom
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CCross

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF

 
def laneCDoublePrimeWideRect (j : Fin 4) : MarkedRect :=
  match j.val with
  | 0 => ⟨-2, 2, 5, 1, true⟩
  | 1 => ⟨-2, -2, 5, 1, true⟩
  | 2 => ⟨-2, -2, 1, 5, false⟩
  | _ => ⟨2, -2, 1, 5, false⟩

 
theorem laneC_double_prime_wide_rect_subset (j : Fin 4) :
    (laneCDoublePrimeWideRect j).toSet ⊆ laneCDoublePrimeCross := by
  have hinner : interior laneCInnerCluster =
      Ioo (-1 : ℝ) 2 ×ℂ Ioo (-1 : ℝ) 2 := by
    simp [laneCInnerCluster, Complex.interior_reProdIm, interior_Icc]
  intro z hz
  fin_cases j <;>
    simp only [laneCDoublePrimeWideRect, MarkedRect.toSet, laneCDoublePrimeCross,
      laneCOuterCluster, hinner, Complex.mem_reProdIm, mem_sdiff, mem_Icc,
      mem_Ioo] at hz ⊢ <;>
    rcases hz with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
  all_goals
    constructor
    · exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    · intro h
      rcases h with ⟨⟨_, _⟩, ⟨_, _⟩⟩
      linarith

 

theorem laneC_double_prime_wide_corners
    {top bot left right : ℝ → ℂ}
    (htop : AdmPath (laneCDoublePrimeWideRect 0).toSet
      (laneCDoublePrimeWideRect 0).side₁
      (laneCDoublePrimeWideRect 0).side₂ top)
    (hbot : AdmPath (laneCDoublePrimeWideRect 1).toSet
      (laneCDoublePrimeWideRect 1).side₁
      (laneCDoublePrimeWideRect 1).side₂ bot)
    (hleft : AdmPath (laneCDoublePrimeWideRect 2).toSet
      (laneCDoublePrimeWideRect 2).side₁
      (laneCDoublePrimeWideRect 2).side₂ left)
    (hright : AdmPath (laneCDoublePrimeWideRect 3).toSet
      (laneCDoublePrimeWideRect 3).side₁
      (laneCDoublePrimeWideRect 3).side₂ right) :
    (∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, top s = left t) ∧
    (∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, top s = right t) ∧
    (∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, bot s = left t) ∧
    (∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, bot s = right t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply hv_meet (H := laneCDoublePrimeWideRect 0)
      (V := laneCDoublePrimeWideRect 2)
    all_goals first | assumption | norm_num [laneCDoublePrimeWideRect]
  · apply hv_meet (H := laneCDoublePrimeWideRect 0)
      (V := laneCDoublePrimeWideRect 3)
    all_goals first | assumption | norm_num [laneCDoublePrimeWideRect]
  · apply hv_meet (H := laneCDoublePrimeWideRect 1)
      (V := laneCDoublePrimeWideRect 2)
    all_goals first | assumption | norm_num [laneCDoublePrimeWideRect]
  · apply hv_meet (H := laneCDoublePrimeWideRect 1)
      (V := laneCDoublePrimeWideRect 3)
    all_goals first | assumption | norm_num [laneCDoublePrimeWideRect]

end SupercriticalLQGUniqueness.B2.DG20Conc
