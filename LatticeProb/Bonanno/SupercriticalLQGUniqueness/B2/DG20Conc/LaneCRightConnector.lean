/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRightConnector at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCDoublePrimeConnector

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF

def laneCRightConnector : MarkedRect := ⟨1, 0, 3, 1, true⟩
def laneCRightConnectorMiddle : MarkedRect := ⟨2, 0, 1, 1, true⟩

theorem laneC_right_connector_middle {δ : ℝ → ℂ}
    (hδ : AdmPath laneCRightConnector.toSet
      laneCRightConnector.side₁ laneCRightConnector.side₂ δ) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      AdmPath laneCRightConnectorMiddle.toSet
        laneCRightConnectorMiddle.side₁ laneCRightConnectorMiddle.side₂
        (LFPP.subPath δ a b) ∧
      (LFPP.subPath δ a b) '' Icc (0 : ℝ) 1 ⊆ laneCDoublePrimeCross := by
  obtain ⟨z, hz, w, hw, hδp, hδU⟩ := hδ
  have hδ0 : (δ 0).re = 1 := by
    rw [hδp.source]
    norm_num [laneCRightConnector, MarkedRect.side₁,
      Complex.mem_reProdIm] at hz
    exact hz.1
  have hδ1 : (δ 1).re = 4 := by
    rw [hδp.target]
    norm_num [laneCRightConnector, MarkedRect.side₂,
      Complex.mem_reProdIm] at hw
    exact hw.1
  obtain ⟨a, b, ha0, hab, hb1, ha, hb, hmid⟩ :=
    RectCross.exists_sub_crossing zero_le_one
      (Complex.continuous_re.comp_continuousOn hδp.continuousOn)
      (by norm_num : (2 : ℝ) ≤ 3)
      (by linarith : (δ 0).re ≤ 2)
      (by linarith : 3 ≤ (δ 1).re)
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
      δ t ∈ laneCRightConnectorMiddle.toSet := by
    intro t ht
    have hfull := hδU t (Icc_subset_Icc ha0 hb1 ht)
    have hhorizontal := hmid t ht
    norm_num [laneCRightConnectorMiddle, laneCRightConnector,
      MarkedRect.toSet, Complex.mem_reProdIm] at hfull hhorizontal ⊢
    exact ⟨hhorizontal, hfull.2⟩
  have hmiddle : AdmPath laneCRightConnectorMiddle.toSet
      laneCRightConnectorMiddle.side₁ laneCRightConnectorMiddle.side₂
      (LFPP.subPath δ a b) := by
    refine ⟨δ a, ?_, δ b, ?_,
      LFPP.isPiecewiseC1Path_subPath hδp ha0 hab' hb1, ?_⟩
    · have h := hδrect a ⟨le_rfl, hab⟩
      norm_num [laneCRightConnectorMiddle, MarkedRect.side₁,
        MarkedRect.toSet, Complex.mem_reProdIm] at h ⊢
      exact ⟨ha, h.2⟩
    · have h := hδrect b ⟨hab, le_rfl⟩
      norm_num [laneCRightConnectorMiddle, MarkedRect.side₂,
        MarkedRect.toSet, Complex.mem_reProdIm] at h ⊢
      exact ⟨hb, h.2⟩
    · intro t ht
      exact hδrect _ (hsub t ht)
  refine ⟨a, b, ha0, hab', hb1, hmiddle, ?_⟩
  rintro x ⟨t, ht, rfl⟩
  exact (laneC_double_prime_long_rect_subset (6 : Fin 8))
    (by
      have h := hδrect _ (hsub t ht)
      norm_num [laneCRightConnectorMiddle, laneCDoublePrimeLongRect,
        LFPP.subPath, MarkedRect.toSet, Complex.mem_reProdIm] at h ⊢
      exact ⟨h.1, ⟨by linarith [h.2.1], h.2.2⟩⟩)

theorem laneC_right_connector_meets_both
    {γ₀ γ₁ δ : ℝ → ℂ}
    (hγ₀ : AdmPath (laneCDoublePrimeLongRect 6).toSet
      (laneCDoublePrimeLongRect 6).side₁
      (laneCDoublePrimeLongRect 6).side₂ γ₀)
    (hγ₁ : AdmPath (laneCDoublePrimeLongRect 7).toSet
      (laneCDoublePrimeLongRect 7).side₁
      (laneCDoublePrimeLongRect 7).side₂ γ₁)
    (hδ : AdmPath laneCRightConnector.toSet
      laneCRightConnector.side₁ laneCRightConnector.side₂ δ) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      (LFPP.subPath δ a b) '' Icc (0 : ℝ) 1 ⊆ laneCDoublePrimeCross ∧
      (∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
        γ₀ s = LFPP.subPath δ a b t) ∧
      (∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
        γ₁ s = LFPP.subPath δ a b t) := by
  obtain ⟨a, b, ha0, hab, hb1, hmid, hring⟩ :=
    laneC_right_connector_middle hδ
  have hmeet₀ : ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
      γ₀ s = LFPP.subPath δ a b t := by
    have h : ∃ t ∈ Icc (0 : ℝ) 1, ∃ s ∈ Icc (0 : ℝ) 1,
        LFPP.subPath δ a b t = γ₀ s := by
      apply hv_meet (H := laneCRightConnectorMiddle)
        (V := laneCDoublePrimeLongRect 6)
      all_goals first | assumption | norm_num [laneCRightConnectorMiddle,
        laneCDoublePrimeLongRect]
    obtain ⟨t, ht, s, hs, m⟩ := h
    exact ⟨s, hs, t, ht, m.symm⟩
  have hmeet₁ : ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
      γ₁ s = LFPP.subPath δ a b t := by
    have h : ∃ t ∈ Icc (0 : ℝ) 1, ∃ s ∈ Icc (0 : ℝ) 1,
        LFPP.subPath δ a b t = γ₁ s := by
      apply hv_meet (H := laneCRightConnectorMiddle)
        (V := laneCDoublePrimeLongRect 7)
      all_goals first | assumption | norm_num [laneCRightConnectorMiddle,
        laneCDoublePrimeLongRect]
    obtain ⟨t, ht, s, hs, m⟩ := h
    exact ⟨s, hs, t, ht, m.symm⟩
  exact ⟨a, b, ha0, hab, hb1, hring, hmeet₀, hmeet₁⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
