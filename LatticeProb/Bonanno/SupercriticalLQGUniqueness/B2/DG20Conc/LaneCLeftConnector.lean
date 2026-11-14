/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCLeftConnector at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCDoublePrimeConnector

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF

def laneCLeftConnector : MarkedRect := ⟨-3, 0, 3, 1, true⟩
def laneCLeftConnectorMiddle : MarkedRect := ⟨-2, 0, 1, 1, true⟩

theorem laneC_left_connector_middle {δ : ℝ → ℂ}
    (hδ : AdmPath laneCLeftConnector.toSet
      laneCLeftConnector.side₁ laneCLeftConnector.side₂ δ) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      AdmPath laneCLeftConnectorMiddle.toSet
        laneCLeftConnectorMiddle.side₁ laneCLeftConnectorMiddle.side₂
        (LFPP.subPath δ a b) ∧
      (LFPP.subPath δ a b) '' Icc (0 : ℝ) 1 ⊆ laneCDoublePrimeCross := by
  obtain ⟨z, hz, w, hw, hδp, hδU⟩ := hδ
  have hδ0 : (δ 0).re = -3 := by
    rw [hδp.source]
    norm_num [laneCLeftConnector, MarkedRect.side₁,
      Complex.mem_reProdIm] at hz
    exact hz.1
  have hδ1 : (δ 1).re = 0 := by
    rw [hδp.target]
    norm_num [laneCLeftConnector, MarkedRect.side₂,
      Complex.mem_reProdIm] at hw
    exact hw.1
  obtain ⟨a, b, ha0, hab, hb1, ha, hb, hmid⟩ :=
    RectCross.exists_sub_crossing zero_le_one
      (Complex.continuous_re.comp_continuousOn hδp.continuousOn)
      (by norm_num : (-2 : ℝ) ≤ -1)
      (by linarith : (δ 0).re ≤ -2)
      (by linarith : -1 ≤ (δ 1).re)
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
      δ t ∈ laneCLeftConnectorMiddle.toSet := by
    intro t ht
    have hfull := hδU t (Icc_subset_Icc ha0 hb1 ht)
    have hhorizontal := hmid t ht
    norm_num [laneCLeftConnectorMiddle, laneCLeftConnector,
      MarkedRect.toSet, Complex.mem_reProdIm] at hfull hhorizontal ⊢
    exact ⟨hhorizontal, hfull.2⟩
  have hmiddle : AdmPath laneCLeftConnectorMiddle.toSet
      laneCLeftConnectorMiddle.side₁ laneCLeftConnectorMiddle.side₂
      (LFPP.subPath δ a b) := by
    refine ⟨δ a, ?_, δ b, ?_,
      LFPP.isPiecewiseC1Path_subPath hδp ha0 hab' hb1, ?_⟩
    · have h := hδrect a ⟨le_rfl, hab⟩
      norm_num [laneCLeftConnectorMiddle, MarkedRect.side₁,
        MarkedRect.toSet, Complex.mem_reProdIm] at h ⊢
      exact ⟨ha, h.2⟩
    · have h := hδrect b ⟨hab, le_rfl⟩
      norm_num [laneCLeftConnectorMiddle, MarkedRect.side₂,
        MarkedRect.toSet, Complex.mem_reProdIm] at h ⊢
      exact ⟨hb, h.2⟩
    · intro t ht
      exact hδrect _ (hsub t ht)
  refine ⟨a, b, ha0, hab', hb1, hmiddle, ?_⟩
  rintro x ⟨t, ht, rfl⟩
  exact (laneC_double_prime_long_rect_subset (4 : Fin 8))
    (by
      have h := hδrect _ (hsub t ht)
      norm_num [laneCLeftConnectorMiddle, laneCDoublePrimeLongRect,
        LFPP.subPath, MarkedRect.toSet, Complex.mem_reProdIm] at h ⊢
      exact ⟨h.1, ⟨by linarith [h.2.1], h.2.2⟩⟩)

theorem laneC_left_connector_meets_both
    {γ₀ γ₁ δ : ℝ → ℂ}
    (hγ₀ : AdmPath (laneCDoublePrimeLongRect 4).toSet
      (laneCDoublePrimeLongRect 4).side₁
      (laneCDoublePrimeLongRect 4).side₂ γ₀)
    (hγ₁ : AdmPath (laneCDoublePrimeLongRect 5).toSet
      (laneCDoublePrimeLongRect 5).side₁
      (laneCDoublePrimeLongRect 5).side₂ γ₁)
    (hδ : AdmPath laneCLeftConnector.toSet
      laneCLeftConnector.side₁ laneCLeftConnector.side₂ δ) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      (LFPP.subPath δ a b) '' Icc (0 : ℝ) 1 ⊆ laneCDoublePrimeCross ∧
      (∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
        γ₀ s = LFPP.subPath δ a b t) ∧
      (∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
        γ₁ s = LFPP.subPath δ a b t) := by
  obtain ⟨a, b, ha0, hab, hb1, hmid, hring⟩ :=
    laneC_left_connector_middle hδ
  have hmeet₀ : ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
      γ₀ s = LFPP.subPath δ a b t := by
    have h : ∃ t ∈ Icc (0 : ℝ) 1, ∃ s ∈ Icc (0 : ℝ) 1,
        LFPP.subPath δ a b t = γ₀ s := by
      apply hv_meet (H := laneCLeftConnectorMiddle)
        (V := laneCDoublePrimeLongRect 4)
      all_goals first | assumption | norm_num [laneCLeftConnectorMiddle,
        laneCDoublePrimeLongRect]
    obtain ⟨t, ht, s, hs, m⟩ := h
    exact ⟨s, hs, t, ht, m.symm⟩
  have hmeet₁ : ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
      γ₁ s = LFPP.subPath δ a b t := by
    have h : ∃ t ∈ Icc (0 : ℝ) 1, ∃ s ∈ Icc (0 : ℝ) 1,
        LFPP.subPath δ a b t = γ₁ s := by
      apply hv_meet (H := laneCLeftConnectorMiddle)
        (V := laneCDoublePrimeLongRect 5)
      all_goals first | assumption | norm_num [laneCLeftConnectorMiddle,
        laneCDoublePrimeLongRect]
    obtain ⟨t, ht, s, hs, m⟩ := h
    exact ⟨s, hs, t, ht, m.symm⟩
  exact ⟨a, b, ha0, hab, hb1, hring, hmeet₀, hmeet₁⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
