/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCTwelveRects at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSquareAround
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DiamGeo

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF

def laneCDoublePrimeTwelveRect (j : Fin 12) : MarkedRect :=
  if h : j.val < 8 then laneCDoublePrimeLongRect ⟨j.val, h⟩ else
    match j.val with
    | 8 => laneCTopConnector
    | 9 => laneCBottomConnector
    | 10 => laneCLeftConnector
    | _ => laneCRightConnector

theorem laneC_twelve_rect_nonneg (j : Fin 12) :
    0 ≤ (laneCDoublePrimeTwelveRect j).w ∧
      0 ≤ (laneCDoublePrimeTwelveRect j).h := by
  fin_cases j <;>
    norm_num [laneCDoublePrimeTwelveRect, laneCDoublePrimeLongRect,
      laneCTopConnector, laneCBottomConnector,
      laneCLeftConnector, laneCRightConnector]

theorem laneC_twelve_rect_len_ne_top {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) (j : Fin 12) :
    rectLen ξ f (laneCDoublePrimeTwelveRect j) ≠ ⊤ :=
  rectLen_ne_top _ (laneC_twelve_rect_nonneg j).1
    (laneC_twelve_rect_nonneg j).2 hf

theorem laneC_twelve_rect_near_paths {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Fin 12 → ℝ → ℂ,
      ∀ j : Fin 12,
        AdmPath (laneCDoublePrimeTwelveRect j).toSet
          (laneCDoublePrimeTwelveRect j).side₁
          (laneCDoublePrimeTwelveRect j).side₂ (p j) ∧
        lfppLen ξ f (p j) ≤
          rectLen ξ f (laneCDoublePrimeTwelveRect j) + ENNReal.ofReal ε := by
  have hnear : ∀ j : Fin 12, ∃ p : ℝ → ℂ,
      AdmPath (laneCDoublePrimeTwelveRect j).toSet
        (laneCDoublePrimeTwelveRect j).side₁
        (laneCDoublePrimeTwelveRect j).side₂ p ∧
      lfppLen ξ f p ≤
        rectLen ξ f (laneCDoublePrimeTwelveRect j) + ENNReal.ofReal ε := by
    intro j
    exact S6D.exists_near (laneC_twelve_rect_len_ne_top hf j) hε
  choose p hp using hnear
  exact ⟨p, hp⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
