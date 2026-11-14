/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCBottomConnector at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCDoublePrimeConnector

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF

def laneCBottomConnector : MarkedRect := ⟨0, -3, 1, 3, false⟩
def laneCBottomConnectorMiddle : MarkedRect := ⟨0, -2, 1, 1, false⟩

theorem laneC_bottom_connector_middle {δ : ℝ → ℂ}
    (hδ : AdmPath laneCBottomConnector.toSet
      laneCBottomConnector.side₁ laneCBottomConnector.side₂ δ) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      AdmPath laneCBottomConnectorMiddle.toSet
        laneCBottomConnectorMiddle.side₁ laneCBottomConnectorMiddle.side₂
        (LFPP.subPath δ a b) ∧
      (LFPP.subPath δ a b) '' Icc (0 : ℝ) 1 ⊆ laneCDoublePrimeCross := by
  obtain ⟨z, hz, w, hw, hδp, hδU⟩ := hδ
  have hδ0 : (δ 0).im = -3 := by
    rw [hδp.source]
    norm_num [laneCBottomConnector, MarkedRect.side₁,
      Complex.mem_reProdIm] at hz
    exact hz.2
  have hδ1 : (δ 1).im = 0 := by
    rw [hδp.target]
    norm_num [laneCBottomConnector, MarkedRect.side₂,
      Complex.mem_reProdIm] at hw
    exact hw.2
  obtain ⟨a, b, ha0, hab, hb1, ha, hb, hmid⟩ :=
    RectCross.exists_sub_crossing zero_le_one
      (Complex.continuous_im.comp_continuousOn hδp.continuousOn)
      (by norm_num : (-2 : ℝ) ≤ -1)
      (by linarith : (δ 0).im ≤ -2)
      (by linarith : -1 ≤ (δ 1).im)
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
      δ t ∈ laneCBottomConnectorMiddle.toSet := by
    intro t ht
    have hfull := hδU t (Icc_subset_Icc ha0 hb1 ht)
    have hvertical := hmid t ht
    norm_num [laneCBottomConnectorMiddle, laneCBottomConnector,
      MarkedRect.toSet, Complex.mem_reProdIm] at hfull hvertical ⊢
    exact ⟨hfull.1, hvertical⟩
  have hmiddle : AdmPath laneCBottomConnectorMiddle.toSet
      laneCBottomConnectorMiddle.side₁ laneCBottomConnectorMiddle.side₂
      (LFPP.subPath δ a b) := by
    refine ⟨δ a, ?_, δ b, ?_,
      LFPP.isPiecewiseC1Path_subPath hδp ha0 hab' hb1, ?_⟩
    · have h := hδrect a ⟨le_rfl, hab⟩
      norm_num [laneCBottomConnectorMiddle, MarkedRect.side₁,
        MarkedRect.toSet, Complex.mem_reProdIm] at h ⊢
      exact ⟨h.1, ha⟩
    · have h := hδrect b ⟨hab, le_rfl⟩
      norm_num [laneCBottomConnectorMiddle, MarkedRect.side₂,
        MarkedRect.toSet, Complex.mem_reProdIm] at h ⊢
      exact ⟨h.1, hb⟩
    · intro t ht
      exact hδrect _ (hsub t ht)
  refine ⟨a, b, ha0, hab', hb1, hmiddle, ?_⟩
  rintro x ⟨t, ht, rfl⟩
  exact (laneC_double_prime_long_rect_subset (2 : Fin 8))
    (by
      have h := hδrect _ (hsub t ht)
      norm_num [laneCBottomConnectorMiddle, laneCDoublePrimeLongRect,
        LFPP.subPath, MarkedRect.toSet, Complex.mem_reProdIm] at h ⊢
      exact ⟨⟨by linarith [h.1.1], by linarith [h.1.2]⟩, h.2⟩)

theorem laneC_bottom_connector_meets_both
    {γ₀ γ₁ δ : ℝ → ℂ}
    (hγ₀ : AdmPath (laneCDoublePrimeLongRect 2).toSet
      (laneCDoublePrimeLongRect 2).side₁
      (laneCDoublePrimeLongRect 2).side₂ γ₀)
    (hγ₁ : AdmPath (laneCDoublePrimeLongRect 3).toSet
      (laneCDoublePrimeLongRect 3).side₁
      (laneCDoublePrimeLongRect 3).side₂ γ₁)
    (hδ : AdmPath laneCBottomConnector.toSet
      laneCBottomConnector.side₁ laneCBottomConnector.side₂ δ) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      (LFPP.subPath δ a b) '' Icc (0 : ℝ) 1 ⊆ laneCDoublePrimeCross ∧
      (∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
        γ₀ s = LFPP.subPath δ a b t) ∧
      (∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
        γ₁ s = LFPP.subPath δ a b t) := by
  obtain ⟨a, b, ha0, hab, hb1, hmid, hring⟩ :=
    laneC_bottom_connector_middle hδ
  have hmeet₀ : ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
      γ₀ s = LFPP.subPath δ a b t := by
    apply hv_meet (H := laneCDoublePrimeLongRect 2)
      (V := laneCBottomConnectorMiddle)
    all_goals first | assumption | norm_num [laneCDoublePrimeLongRect,
      laneCBottomConnectorMiddle]
  have hmeet₁ : ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
      γ₁ s = LFPP.subPath δ a b t := by
    apply hv_meet (H := laneCDoublePrimeLongRect 3)
      (V := laneCBottomConnectorMiddle)
    all_goals first | assumption | norm_num [laneCDoublePrimeLongRect,
      laneCBottomConnectorMiddle]
  exact ⟨a, b, ha0, hab, hb1, hring, hmeet₀, hmeet₁⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
