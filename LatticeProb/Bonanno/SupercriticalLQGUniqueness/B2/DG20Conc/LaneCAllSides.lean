/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAllSides at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCTopBridge
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCBottomBridge
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCLeftBridge
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRightBridge

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

 
theorem laneC_four_wide_of_twelve_long {ξ : ℝ} {f : ℂ → ℝ}
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
    ∃ top bot left right : ℝ → ℂ,
      AdmPath (laneCDoublePrimeWideRect 0).toSet
        (laneCDoublePrimeWideRect 0).side₁
        (laneCDoublePrimeWideRect 0).side₂ top ∧
      AdmPath (laneCDoublePrimeWideRect 1).toSet
        (laneCDoublePrimeWideRect 1).side₁
        (laneCDoublePrimeWideRect 1).side₂ bot ∧
      AdmPath (laneCDoublePrimeWideRect 2).toSet
        (laneCDoublePrimeWideRect 2).side₁
        (laneCDoublePrimeWideRect 2).side₂ left ∧
      AdmPath (laneCDoublePrimeWideRect 3).toSet
        (laneCDoublePrimeWideRect 3).side₁
        (laneCDoublePrimeWideRect 3).side₂ right ∧
      lfppLen ξ f top ≤ lfppLen ξ f (γ 0) + lfppLen ξ f δtop + lfppLen ξ f (γ 1) ∧
      lfppLen ξ f bot ≤ lfppLen ξ f (γ 2) + lfppLen ξ f δbot + lfppLen ξ f (γ 3) ∧
      lfppLen ξ f left ≤ lfppLen ξ f (γ 4) + lfppLen ξ f δleft + lfppLen ξ f (γ 5) ∧
      lfppLen ξ f right ≤ lfppLen ξ f (γ 6) + lfppLen ξ f δright + lfppLen ξ f (γ 7) := by
  obtain ⟨top, _, _, hT, hTc⟩ := laneC_top_side_bridge_wide (hγ 0) (hγ 1) htop
  obtain ⟨bot, hB, hBc⟩ := laneC_bottom_side_bridge_wide (hγ 2) (hγ 3) hbot
  obtain ⟨left, hL, hLc⟩ := laneC_left_side_bridge_wide (hγ 4) (hγ 5) hleft
  obtain ⟨right, hR, hRc⟩ := laneC_right_side_bridge_wide (hγ 6) (hγ 7) hright
  exact ⟨top, bot, left, right, hT, hB, hL, hR, hTc, hBc, hLc, hRc⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
