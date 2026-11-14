/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeHorizontalClip at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeLongRects
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross
import LatticeProb.Bonanno.LQGMetric.LFPP.PathOps

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

def laneCPrimeHorizontalConnector (x y : ℝ) : MarkedRect :=
  ⟨x, y, 3 / 8, 1 / 8, true⟩

def laneCPrimeHorizontalConnectorMid (x y : ℝ) : MarkedRect :=
  ⟨x + 1 / 16, y, 1 / 8, 1 / 8, true⟩

theorem laneC_prime_horizontal_connector_middle {x y : ℝ} {δ : ℝ → ℂ}
    (hδ : AdmPath (laneCPrimeHorizontalConnector x y).toSet
      (laneCPrimeHorizontalConnector x y).side₁
      (laneCPrimeHorizontalConnector x y).side₂ δ) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      AdmPath (laneCPrimeHorizontalConnectorMid x y).toSet
        (laneCPrimeHorizontalConnectorMid x y).side₁
        (laneCPrimeHorizontalConnectorMid x y).side₂
        (subPath δ a b) := by
  obtain ⟨z, hz, w, hw, hδp, hδU⟩ := hδ
  have hδ0 : (δ 0).re = x := by
    rw [hδp.source]
    norm_num [laneCPrimeHorizontalConnector, MarkedRect.side₁,
      Complex.mem_reProdIm] at hz
    exact hz.1
  have hδ1 : (δ 1).re = x + 3 / 8 := by
    rw [hδp.target]
    norm_num [laneCPrimeHorizontalConnector, MarkedRect.side₂,
      Complex.mem_reProdIm] at hw
    exact hw.1
  obtain ⟨a, b, ha0, hab, hb1, ha, hb, hmid⟩ :=
    RectCross.exists_sub_crossing zero_le_one
      (Complex.continuous_re.comp_continuousOn hδp.continuousOn)
      (by norm_num : x + (1 / 16 : ℝ) ≤ x + 3 / 16)
      (by linarith : (δ 0).re ≤ x + 1 / 16)
      (by linarith : x + 3 / 16 ≤ (δ 1).re)
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
      δ t ∈ (laneCPrimeHorizontalConnectorMid x y).toSet := by
    intro t ht
    have hfull := hδU t (Icc_subset_Icc ha0 hb1 ht)
    have hvertical := hmid t ht
    norm_num [laneCPrimeHorizontalConnectorMid, laneCPrimeHorizontalConnector,
      MarkedRect.toSet, Complex.mem_reProdIm] at hfull hvertical ⊢
    exact ⟨⟨hvertical.1, by linarith [hvertical.2]⟩, hfull.2⟩
  have hM : AdmPath (laneCPrimeHorizontalConnectorMid x y).toSet
      (laneCPrimeHorizontalConnectorMid x y).side₁
      (laneCPrimeHorizontalConnectorMid x y).side₂ (subPath δ a b) := by
    refine ⟨δ a, ?_, δ b, ?_,
      isPiecewiseC1Path_subPath hδp ha0 hab' hb1, ?_⟩
    · have h := hδrect a ⟨le_rfl, hab⟩
      norm_num [laneCPrimeHorizontalConnectorMid, MarkedRect.side₁,
        MarkedRect.toSet, Complex.mem_reProdIm] at h ⊢
      exact ⟨ha, h.2⟩
    · have h := hδrect b ⟨hab, le_rfl⟩
      norm_num [laneCPrimeHorizontalConnectorMid, MarkedRect.side₂,
        MarkedRect.toSet, Complex.mem_reProdIm] at h ⊢
      change (δ b).re = x + 3 / 16 at hb
      exact ⟨by linarith [hb], h.2⟩
    · intro t ht
      exact hδrect _ (hsub t ht)
  exact ⟨a, b, ha0, hab', hb1, hM⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
