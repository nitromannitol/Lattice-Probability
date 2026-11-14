/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeTopClip at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeLongRects
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross
import LatticeProb.Bonanno.LQGMetric.LFPP.PathOps

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

def laneCPrimeVerticalConnector (x y : ℝ) : MarkedRect :=
  ⟨x, y, 1 / 8, 3 / 8, false⟩

def laneCPrimeVerticalConnectorMid (x y : ℝ) : MarkedRect :=
  ⟨x, y + 1 / 16, 1 / 8, 1 / 8, false⟩

theorem laneC_prime_vertical_connector_middle {x y : ℝ} {δ : ℝ → ℂ}
    (hδ : AdmPath (laneCPrimeVerticalConnector x y).toSet
      (laneCPrimeVerticalConnector x y).side₁
      (laneCPrimeVerticalConnector x y).side₂ δ) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      AdmPath (laneCPrimeVerticalConnectorMid x y).toSet
        (laneCPrimeVerticalConnectorMid x y).side₁
        (laneCPrimeVerticalConnectorMid x y).side₂
        (subPath δ a b) := by
  obtain ⟨z, hz, w, hw, hδp, hδU⟩ := hδ
  have hδ0 : (δ 0).im = y := by
    rw [hδp.source]
    norm_num [laneCPrimeVerticalConnector, MarkedRect.side₁,
      Complex.mem_reProdIm] at hz
    exact hz.2
  have hδ1 : (δ 1).im = y + 3 / 8 := by
    rw [hδp.target]
    norm_num [laneCPrimeVerticalConnector, MarkedRect.side₂,
      Complex.mem_reProdIm] at hw
    exact hw.2
  obtain ⟨a, b, ha0, hab, hb1, ha, hb, hmid⟩ :=
    RectCross.exists_sub_crossing zero_le_one
      (Complex.continuous_im.comp_continuousOn hδp.continuousOn)
      (by norm_num : y + (1 / 16 : ℝ) ≤ y + 3 / 16)
      (by linarith : (δ 0).im ≤ y + 1 / 16)
      (by linarith : y + 3 / 16 ≤ (δ 1).im)
  have hab' : a < b := by
    by_contra h
    have heq : a = b := le_antisymm hab (le_of_not_gt h)
    rw [heq] at ha
    linarith
  have hsub : ∀ t ∈ Icc (0 : ℝ) 1,
      (b - a) * t + a ∈ Icc a b := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2]
  have hδrect : ∀ t ∈ Icc a b,
      δ t ∈ (laneCPrimeVerticalConnectorMid x y).toSet := by
    intro t ht
    have hfull := hδU t (Icc_subset_Icc ha0 hb1 ht)
    have hvertical := hmid t ht
    norm_num [laneCPrimeVerticalConnectorMid, laneCPrimeVerticalConnector,
      MarkedRect.toSet, Complex.mem_reProdIm] at hfull hvertical ⊢
    exact ⟨hfull.1, ⟨hvertical.1, by linarith [hvertical.2]⟩⟩
  have hM : AdmPath (laneCPrimeVerticalConnectorMid x y).toSet
      (laneCPrimeVerticalConnectorMid x y).side₁
      (laneCPrimeVerticalConnectorMid x y).side₂ (subPath δ a b) := by
    refine ⟨δ a, ?_, δ b, ?_,
      isPiecewiseC1Path_subPath hδp ha0 hab' hb1, ?_⟩
    · have h := hδrect a ⟨le_rfl, hab⟩
      norm_num [laneCPrimeVerticalConnectorMid, MarkedRect.side₁,
        MarkedRect.toSet, Complex.mem_reProdIm] at h ⊢
      exact ⟨h.1, ha⟩
    · have h := hδrect b ⟨hab, le_rfl⟩
      norm_num [laneCPrimeVerticalConnectorMid, MarkedRect.side₂,
        MarkedRect.toSet, Complex.mem_reProdIm] at h ⊢
      change (δ b).im = y + 3 / 16 at hb
      exact ⟨h.1, by linarith [hb]⟩
    · intro t ht
      exact hδrect _ (hsub t ht)
  exact ⟨a, b, ha0, hab', hb1, hM⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
