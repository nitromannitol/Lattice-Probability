/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBBoundarySiteWalk at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSiteWalk
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBLongCost
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S2Site

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

 




theorem laneB_boundary_site_walk {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) {R bnd : ℝ} (hR : 24 ≤ R)
    (hfamily : ∀ j ∈ laneBLongRects R,
      T20B.mrectLen ξ f 0 j.1 j.2 3 1 ≤ bnd)
    {b : ℤ × ℤ} (hb : b ∈ laneBBoundaryBlocks (laneBGridRadius R))
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ (C : SiteCirc ξ f b (4 * (ENNReal.ofReal bnd + δ)))
      (W : ℝ → ℂ) (a d : ℂ),
      IsPiecewiseC1Path W a d ∧
      MapsTo W (Icc (0 : ℝ) 1)
        {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R} ∧
      (∀ x, C.On x → x ∈ W '' Icc (0 : ℝ) 1) ∧
      lfppLen ξ f W ≤ 3 * (4 * (ENNReal.ofReal bnd + δ)) := by
  have hbnd (i : Fin 4) :
      rectLen ξ f (S6U.siteR b i) ≤ ENNReal.ofReal bnd :=
    laneB_siteR_rectLen_le_of_long_family_bound hf hfamily hb i
  obtain ⟨C⟩ := siteCirc_of_good
    (ξ := ξ) (g := f) (z := b) hδ (by simp : ENNReal.ofReal bnd ≠ ⊤)
    (hbnd 0) (hbnd 1) (hbnd 2) (hbnd 3)
  obtain ⟨W, a, d, hp, hm, ht, hc⟩ :=
    laneB_siteCirc_walk C (laneB_siteCirc_sub_open_annulus hR hb)
  exact ⟨C, W, a, d, hp, hm, ht, hc⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
