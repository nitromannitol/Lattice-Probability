/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBPerimeterWalk at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBChainWalk
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBBoundarySiteWalk
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSiteWalkMeet
import LatticeProb.Bonanno.LQGMetric.Perc.Annulus

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

 



theorem laneB_perimeter_walk {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) {R bnd : ℝ} (hR : 24 ≤ R)
    (hfamily : ∀ j ∈ laneBLongRects R,
      T20B.mrectLen ξ f 0 j.1 j.2 3 1 ≤ bnd)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ (V : ℝ → ℂ) (a d : ℂ),
      IsPiecewiseC1Path V a d ∧
      MapsTo V (Icc (0 : ℝ) 1)
        {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R} ∧
      (∀ b ∈ laneBBoundaryBlocks (laneBGridRadius R),
        ∃ C : SiteCirc ξ f b (4 * (ENNReal.ofReal bnd + δ)),
          ∀ x, C.On x → x ∈ V '' Icc (0 : ℝ) 1) ∧
      lfppLen ξ f V ≤
        (((4 * (2 * laneBGridRadius R + 1)).toNat + 1 : ℕ) : ℝ≥0∞) *
          (3 * (3 * (4 * (ENNReal.ofReal bnd + δ)))) := by
  let m := laneBGridRadius R
  let N := (4 * (2 * m + 1)).toNat
  have hm : 0 ≤ m := by
    have h := (laneB_grid_radius_bounds hR).1
    change 0 ≤ laneBGridRadius R
    have : (0 : ℝ) ≤ (laneBGridRadius R : ℝ) := by linarith
    exact_mod_cast this
  have hNnonneg : 0 ≤ 4 * (2 * m + 1) := by omega
  have hN : (N : ℤ) = 4 * (2 * m + 1) :=
    Int.toNat_of_nonneg hNnonneg
  have hsite (k : ℕ) :
      ∃ (C : SiteCirc ξ f (laneBPerimeterBlock m (min k N))
          (4 * (ENNReal.ofReal bnd + δ)))
        (W : ℝ → ℂ) (a d : ℂ),
        IsPiecewiseC1Path W a d ∧
        MapsTo W (Icc (0 : ℝ) 1)
          {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R} ∧
        (∀ x, C.On x → x ∈ W '' Icc (0 : ℝ) 1) ∧
        lfppLen ξ f W ≤ 3 * (4 * (ENNReal.ofReal bnd + δ)) := by
    have hk : (((min k N : ℕ) : ℤ)) ≤ 4 * (2 * m + 1) := by omega
    have hb := laneB_perimeterBlock_mem hm hk
    exact laneB_boundary_site_walk hf hR hfamily (by simpa only [m] using hb) hδ
  choose C W a d hp hmap htrace hcost using hsite
  have hmeet (k : ℕ) (hk : k < N) :
      ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
        W k s = W (k + 1) t := by
    have hk0 : k ≤ N := Nat.le_of_lt hk
    have hk1 : k + 1 ≤ N := hk
    have hadj : PercAdjK
        (laneBPerimeterBlock m k) (laneBPerimeterBlock m (k + 1)) :=
      percAdjK_of_adj4 (laneB_perimeterBlock_adj hm (by omega))
    exact laneB_siteWalk_meet_adjK (C k) (C (k + 1))
      (htrace k) (htrace (k + 1))
      (by simpa only [Nat.min_eq_left hk0, Nat.min_eq_left hk1] using hadj)
  obtain ⟨V, aV, dV, hpV, hmapV, hcover, hlen⟩ :=
    laneB_chain_walk (N := N) (W := W)
      (fun k _ => ⟨a k, d k, hp k⟩)
      (fun k _ => hmap k) (fun k _ => hcost k) hmeet
  refine ⟨V, aV, dV, hpV, hmapV, ?_, ?_⟩
  · intro b hb
    obtain ⟨k, hk, hbk⟩ := laneB_perimeterBlock_surj hm (by simpa only [m] using hb)
    have hkN : k ≤ N := by omega
    have hselected :
        ∃ C' : SiteCirc ξ f (laneBPerimeterBlock m (min k N))
            (4 * (ENNReal.ofReal bnd + δ)),
          ∀ x, C'.On x → x ∈ V '' Icc (0 : ℝ) 1 := by
      exact ⟨C k, fun x hx => hcover k hkN (htrace k x hx)⟩
    rw [← hbk]
    have hmin : min k N = k := min_eq_left hkN
    rw [hmin] at hselected
    exact hselected
  · simpa only [m, N] using hlen

end SupercriticalLQGUniqueness.B2.DG20Conc
