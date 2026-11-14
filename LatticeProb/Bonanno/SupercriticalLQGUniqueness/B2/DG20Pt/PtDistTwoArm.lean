/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistTwoArm at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistChain
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistSitePathInU
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistTerminal

 


set_option autoImplicit false
noncomputable section

open LQGMetric LQGMetric.LFPP
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_join_two_arms {ξ : ℝ} {f : ℂ → ℝ} {U : Set ℂ}
    (z w zFine zCoarse wFine wCoarse : ℂ)
    (Az Aw B Tz Tw : ℝ≥0∞)
    (hz : lfppDOn ξ f U z zFine ≤ Tz)
    (hza : lfppDOn ξ f U zFine zCoarse ≤ Az)
    (hc : lfppDOn ξ f U zCoarse wCoarse ≤ B)
    (hwa : lfppDOn ξ f U wFine wCoarse ≤ Aw)
    (hw : lfppDOn ξ f U w wFine ≤ Tw) :
    lfppDOn ξ f U z w ≤ Tz + Az + B + Aw + Tw := by
  calc
    lfppDOn ξ f U z w ≤
        lfppDOn ξ f U z zFine + lfppDOn ξ f U zFine w :=
      lfppDOn_triangle _ _ _
    _ ≤ lfppDOn ξ f U z zFine +
        (lfppDOn ξ f U zFine zCoarse + lfppDOn ξ f U zCoarse w) :=
      add_le_add le_rfl (lfppDOn_triangle _ _ _)
    _ ≤ lfppDOn ξ f U z zFine +
        (lfppDOn ξ f U zFine zCoarse +
          (lfppDOn ξ f U zCoarse wCoarse + lfppDOn ξ f U wCoarse w)) :=
      add_le_add le_rfl (add_le_add le_rfl (lfppDOn_triangle _ _ _))
    _ ≤ lfppDOn ξ f U z zFine +
        (lfppDOn ξ f U zFine zCoarse +
          (lfppDOn ξ f U zCoarse wCoarse +
            (lfppDOn ξ f U wCoarse wFine + lfppDOn ξ f U wFine w))) :=
      add_le_add le_rfl (add_le_add le_rfl
        (add_le_add le_rfl (lfppDOn_triangle _ _ _)))
    _ ≤ Tz + (Az + (B + (Aw + Tw))) := by
      rw [lfppDOn_comm wCoarse wFine, lfppDOn_comm wFine w]
      gcongr
    _ = Tz + Az + B + Aw + Tw := by simp only [add_assoc]

end SupercriticalLQGUniqueness.B2.DG20Pt
