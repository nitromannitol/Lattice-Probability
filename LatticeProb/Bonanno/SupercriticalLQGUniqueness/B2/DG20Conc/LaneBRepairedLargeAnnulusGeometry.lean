/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBRepairedLargeAnnulusGeometry at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBLongUpper
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBShortFamily
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneAInputs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRepairedInputs

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

 

theorem laneB_repairedLargeAnnulusGeometry :
    LaneCRepairedInputs.LargeAnnulusGeometry := by
  refine ⟨24, 400, by norm_num, by norm_num, ?_⟩
  intro R hR
  unfold LaneCRepairedInputs.RectAnnulusCoverAt
  obtain ⟨Js, us, cs, hJs, hshort⟩ := laneB_large_annulus_short_family hR
  let Jl := Finset.range (laneBLongRects R).card
  let ul : ℕ → Circle := fun k => (laneBLongEnumerate R k).1
  let cl : ℕ → ℂ := fun k => (laneBLongEnumerate R k).2
  refine ⟨Js, Jl, us, ul, cs, cl, ?_, ?_, ?_⟩
  · have hpos : (0 : ℝ) ≤ R := by linarith
    nlinarith
  · have hJl := laneB_longRects_card_le hR
    have hpos : (0 : ℝ) ≤ R := by linarith
    simpa only [Jl, Finset.card_range] using
      (show ((laneBLongRects R).card : ℝ) ≤ 400 * R by nlinarith)
  · intro ξ f hf a b
    constructor
    · intro hsmall
      exact hshort ξ f a hsmall
    · intro hlarge
      obtain ⟨j, hj, hlt⟩ :=
        laneB_long_rectangle_of_large_around hR ξ f hf b hlarge
      obtain ⟨k, hk, hkj⟩ := laneB_longEnumerate_surj R hj
      exact ⟨k, by simpa only [Jl] using hk,
        by simpa only [ul, cl, hkj] using hlt⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
