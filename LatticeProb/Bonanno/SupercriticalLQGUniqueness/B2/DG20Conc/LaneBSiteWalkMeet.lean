/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSiteWalkMeet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBBoundarySiteWalk
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Glue

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF

 


theorem laneB_siteWalk_meet_adjK {ξ : ℝ} {f : ℂ → ℝ}
    {z z' : ℤ × ℤ} {c c' : ℝ≥0∞}
    (C : SiteCirc ξ f z c) (C' : SiteCirc ξ f z' c')
    {W W' : ℝ → ℂ}
    (hW : ∀ x, C.On x → x ∈ W '' Icc (0 : ℝ) 1)
    (hW' : ∀ x, C'.On x → x ∈ W' '' Icc (0 : ℝ) 1)
    (hadj : PercAdjK z z') :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, W s = W' t := by
  obtain ⟨q, hq, hq'⟩ := SiteCirc.meet_adjK C C' hadj
  obtain ⟨s, hs, es⟩ := hW q hq
  obtain ⟨t, ht, et⟩ := hW' q hq'
  exact ⟨s, hs, t, ht, es.trans et.symm⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
