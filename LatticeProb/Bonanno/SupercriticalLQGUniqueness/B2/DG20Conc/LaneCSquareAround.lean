/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSquareAround at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPushCircuit
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAllSides

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

theorem laneC_four_wide_aroundDist_le {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) {top bot left right : ℝ → ℂ}
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
    (lfppContMetric ξ f hf).aroundDist laneCDoublePrimeAround
      laneCDoublePrimeInner laneCDoublePrimeOuter ≤
      lfppLen ξ f top + lfppLen ξ f bot +
        lfppLen ξ f left + lfppLen ξ f right := by
  obtain ⟨γ, hp, hc, hm, hdeg, hlen⟩ :=
    laneC_four_wide_closed_loop (ξ := ξ) (f := f) htop hbot hleft hright
  exact (laneC_push_closed_loop_aroundDist_le hf hp hc hm hdeg).trans hlen

theorem laneC_twelve_long_aroundDist_le {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f)
    (γ : Fin 8 → ℝ → ℂ) (δtop δbot δleft δright : ℝ → ℂ)
    (hγ : ∀ j : Fin 8,
      AdmPath (laneCDoublePrimeLongRect j).toSet
        (laneCDoublePrimeLongRect j).side₁
        (laneCDoublePrimeLongRect j).side₂ (γ j))
    (htop : AdmPath laneCTopConnector.toSet
      laneCTopConnector.side₁ laneCTopConnector.side₂ δtop)
    (hbot : AdmPath laneCBottomConnector.toSet
      laneCBottomConnector.side₁ laneCBottomConnector.side₂ δbot)
    (hleft : AdmPath laneCLeftConnector.toSet
      laneCLeftConnector.side₁ laneCLeftConnector.side₂ δleft)
    (hright : AdmPath laneCRightConnector.toSet
      laneCRightConnector.side₁ laneCRightConnector.side₂ δright) :
    (lfppContMetric ξ f hf).aroundDist laneCDoublePrimeAround
      laneCDoublePrimeInner laneCDoublePrimeOuter ≤
      (lfppLen ξ f (γ 0) + lfppLen ξ f δtop + lfppLen ξ f (γ 1)) +
      (lfppLen ξ f (γ 2) + lfppLen ξ f δbot + lfppLen ξ f (γ 3)) +
      (lfppLen ξ f (γ 4) + lfppLen ξ f δleft + lfppLen ξ f (γ 5)) +
      (lfppLen ξ f (γ 6) + lfppLen ξ f δright + lfppLen ξ f (γ 7)) := by
  obtain ⟨top, bot, left, right, hT, hB, hL, hR, hcT, hcB, hcL, hcR⟩ :=
    laneC_four_wide_of_twelve_long γ δtop δbot δleft δright hγ htop hbot hleft hright
  calc
    _ ≤ lfppLen ξ f top + lfppLen ξ f bot +
        lfppLen ξ f left + lfppLen ξ f right :=
      laneC_four_wide_aroundDist_le hf hT hB hL hR
    _ = (lfppLen ξ f top + lfppLen ξ f bot) +
        (lfppLen ξ f left + lfppLen ξ f right) := by ac_rfl
    _ ≤ ((lfppLen ξ f (γ 0) + lfppLen ξ f δtop + lfppLen ξ f (γ 1)) +
        (lfppLen ξ f (γ 2) + lfppLen ξ f δbot + lfppLen ξ f (γ 3))) +
        ((lfppLen ξ f (γ 4) + lfppLen ξ f δleft + lfppLen ξ f (γ 5)) +
        (lfppLen ξ f (γ 6) + lfppLen ξ f δright + lfppLen ξ f (γ 7))) :=
      add_le_add (add_le_add hcT hcB) (add_le_add hcL hcR)
    _ = _ := by ac_rfl

end SupercriticalLQGUniqueness.B2.DG20Conc
