/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCTopBridge at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCGlue4LFPP
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCDoublePrimeConnector
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCDoublePrimeWide

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

theorem laneC_top_side_bridge_wide {ξ : ℝ} {f : ℂ → ℝ}
    {γ₀ γ₁ δ : ℝ → ℂ}
    (hγ₀ : AdmPath (laneCDoublePrimeLongRect 0).toSet
      (laneCDoublePrimeLongRect 0).side₁
      (laneCDoublePrimeLongRect 0).side₂ γ₀)
    (hγ₁ : AdmPath (laneCDoublePrimeLongRect 1).toSet
      (laneCDoublePrimeLongRect 1).side₁
      (laneCDoublePrimeLongRect 1).side₂ γ₁)
    (hδ : AdmPath laneCTopConnector.toSet
      laneCTopConnector.side₁ laneCTopConnector.side₂ δ) :
    ∃ P : ℝ → ℂ,
      IsPiecewiseC1Path P (γ₀ 0) (γ₁ 1) ∧
      MapsTo P (Icc (0 : ℝ) 1) laneCDoublePrimeCross ∧
      AdmPath (laneCDoublePrimeWideRect 0).toSet
        (laneCDoublePrimeWideRect 0).side₁
        (laneCDoublePrimeWideRect 0).side₂ P ∧
      lfppLen ξ f P ≤ lfppLen ξ f γ₀ + lfppLen ξ f δ + lfppLen ξ f γ₁ := by
  obtain ⟨a, b, ha, hab, hb, hδring,
    ⟨s₀, hs₀, t₀, ht₀, m₀⟩, ⟨s₁, hs₁, t₁, ht₁, m₁⟩⟩ :=
    laneC_top_connector_meets_both hγ₀ hγ₁ hδ
  obtain ⟨z₀, hz₀, w₀, hw₀, hγ₀p, hγ₀map⟩ := hγ₀
  obtain ⟨z₁, hz₁, w₁, hw₁, hγ₁p, hγ₁map⟩ := hγ₁
  obtain ⟨zd, hzd, wd, hwd, hδp, hδmap⟩ := hδ
  let δ' := subPath δ a b
  let g₀ := Strong.seg γ₀ 0 s₀
  let g₁ := Strong.seg δ' t₀ t₁
  let g₂ := Strong.seg γ₁ s₁ 1
  let g₃ : ℝ → ℂ := fun _ => γ₁ 1
  let P := laneCConcat4 g₀ g₁ g₂ g₃
  have hγ₀p' : IsPiecewiseC1Path γ₀ (γ₀ 0) (γ₀ 1) := by
    simpa only [hγ₀p.source, hγ₀p.target] using hγ₀p
  have hγ₁p' : IsPiecewiseC1Path γ₁ (γ₁ 0) (γ₁ 1) := by
    simpa only [hγ₁p.source, hγ₁p.target] using hγ₁p
  have hδp' : IsPiecewiseC1Path δ' (δ' 0) (δ' 1) := by
    convert isPiecewiseC1Path_subPath hδp ha hab hb using 1 <;>
      simp [δ', subPath]
  have hm₀₁ : g₀ 1 = g₁ 0 := by simpa [g₀, g₁, δ'] using m₀
  have hm₁₂ : g₁ 1 = g₂ 0 := by simpa [g₁, g₂, δ'] using m₁.symm
  have hm₂₃ : g₂ 1 = g₃ 0 := by simp [g₂, g₃]
  have hgp₀ : IsPiecewiseC1Path g₀ (g₀ 0) (g₀ 1) := by
    simpa [g₀] using laneC_strong_seg_piecewise hγ₀p' (by norm_num : (0 : ℝ) ∈ Icc 0 1) hs₀
  have hgp₁ : IsPiecewiseC1Path g₁ (g₁ 0) (g₁ 1) := by
    simpa [g₁] using laneC_strong_seg_piecewise hδp' ht₀ ht₁
  have hgp₂ : IsPiecewiseC1Path g₂ (g₂ 0) (g₂ 1) := by
    simpa [g₂] using laneC_strong_seg_piecewise hγ₁p' hs₁ (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  have hgp₃ : IsPiecewiseC1Path g₃ (g₃ 0) (g₃ 1) := by
    simpa [g₃] using LQGMetric.DDDF.isPiecewiseC1Path_const (γ₁ 1)
  have hP : IsPiecewiseC1Path P (g₀ 0) (g₃ 1) :=
    laneC_concat4_piecewise hgp₀
      (by simpa only [hm₀₁] using hgp₁)
      (by simpa only [hm₁₂] using hgp₂)
      (by simpa only [hm₂₃] using hgp₃)
  have hmap₀ : MapsTo γ₀ (Icc (0 : ℝ) 1) laneCDoublePrimeCross :=
    fun t ht => laneC_double_prime_long_rect_subset 0 (hγ₀map t ht)
  have hmap₁ : MapsTo γ₁ (Icc (0 : ℝ) 1) laneCDoublePrimeCross :=
    fun t ht => laneC_double_prime_long_rect_subset 1 (hγ₁map t ht)
  have hmapδ : MapsTo δ' (Icc (0 : ℝ) 1) laneCDoublePrimeCross :=
    fun t ht => hδring ⟨t, ht, rfl⟩
  have hPmap : MapsTo P (Icc (0 : ℝ) 1) laneCDoublePrimeCross := by
    apply laneC_concat4_mapsTo
    · exact Strong.mapsTo_seg hmap₀ (by norm_num) hs₀
    · exact Strong.mapsTo_seg hmapδ ht₀ ht₁
    · exact Strong.mapsTo_seg hmap₁ hs₁ (by norm_num)
    · intro t ht
      exact hmap₁ (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  have hlen : lfppLen ξ f P ≤ lfppLen ξ f γ₀ + lfppLen ξ f δ +
      lfppLen ξ f γ₁ := by
    rw [laneC_concat4_length hm₀₁ hm₁₂ hm₂₃]
    have hδlen : lfppLen ξ f δ' ≤ lfppLen ξ f δ :=
      laneC_subpath_len_le ha hab hb
    have h₀len : lfppLen ξ f g₀ ≤ lfppLen ξ f γ₀ :=
      laneC_strong_seg_len_le γ₀ (by norm_num) hs₀
    have h₁len : lfppLen ξ f g₁ ≤ lfppLen ξ f δ :=
      (laneC_strong_seg_len_le δ' ht₀ ht₁).trans hδlen
    have h₂len : lfppLen ξ f g₂ ≤ lfppLen ξ f γ₁ :=
      laneC_strong_seg_len_le γ₁ hs₁ (by norm_num)
    rw [show lfppLen ξ f g₃ = 0 by exact LQGMetric.DDDF.lfppLen_const _]
    simpa only [add_zero] using add_le_add (add_le_add h₀len h₁len) h₂len
  have htop₀ : MapsTo γ₀ (Icc (0 : ℝ) 1)
      (laneCDoublePrimeWideRect 0).toSet := by
    intro t ht
    have h := hγ₀map t ht
    norm_num [laneCDoublePrimeLongRect, laneCDoublePrimeWideRect,
      MarkedRect.toSet, Complex.mem_reProdIm] at h ⊢
    exact ⟨⟨h.1.1, by linarith [h.1.2]⟩, h.2⟩
  have htop₁ : MapsTo γ₁ (Icc (0 : ℝ) 1)
      (laneCDoublePrimeWideRect 0).toSet := by
    intro t ht
    have h := hγ₁map t ht
    norm_num [laneCDoublePrimeLongRect, laneCDoublePrimeWideRect,
      MarkedRect.toSet, Complex.mem_reProdIm] at h ⊢
    exact ⟨⟨by linarith [h.1.1], h.1.2⟩, h.2⟩
  have htopδ : MapsTo δ' (Icc (0 : ℝ) 1)
      (laneCDoublePrimeWideRect 0).toSet := by
    intro t ht
    have htime : (b - a) * t + a ∈ Icc (0 : ℝ) 1 :=
      ⟨by nlinarith [ht.1, ht.2, ha], by nlinarith [ht.1, ht.2, hb]⟩
    have hfull := hδmap _ htime
    have hring := hδring ⟨t, ht, rfl⟩
    have hinner : interior laneCInnerCluster =
        Ioo (-1 : ℝ) 2 ×ℂ Ioo (-1 : ℝ) 2 := by
      simp [laneCInnerCluster, Complex.interior_reProdIm, interior_Icc]
    have houter := hring.1
    have hnot := hring.2
    rw [hinner] at hnot
    simp only [Complex.mem_reProdIm, mem_Ioo] at hnot
    norm_num [laneCTopConnector, MarkedRect.toSet,
      Complex.mem_reProdIm] at hfull
    simp only [laneCOuterCluster, Complex.mem_reProdIm, mem_Icc] at houter
    dsimp [δ', subPath] at hnot houter
    have hyge : 2 ≤ (δ' t).im := by
      by_contra h
      dsimp [δ', subPath] at h
      apply hnot
      exact ⟨⟨by linarith [hfull.1.1], by linarith [hfull.1.2]⟩,
        ⟨by linarith [hfull.2.1], by linarith⟩⟩
    norm_num [laneCDoublePrimeWideRect, MarkedRect.toSet,
      Complex.mem_reProdIm]
    dsimp [δ', subPath]
    exact ⟨⟨by linarith [hfull.1.1], by linarith [hfull.1.2]⟩,
      ⟨hyge, by linarith [houter.2.2]⟩⟩
  have hPwide : MapsTo P (Icc (0 : ℝ) 1)
      (laneCDoublePrimeWideRect 0).toSet := by
    apply laneC_concat4_mapsTo
    · exact Strong.mapsTo_seg htop₀ (by norm_num) hs₀
    · exact Strong.mapsTo_seg htopδ ht₀ ht₁
    · exact Strong.mapsTo_seg htop₁ hs₁ (by norm_num)
    · intro t ht
      exact htop₁ (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  have hg₀ : g₀ 0 = γ₀ 0 := by simp [g₀]
  have hg₃ : g₃ 1 = γ₁ 1 := rfl
  have hPpiece : IsPiecewiseC1Path P (γ₀ 0) (γ₁ 1) := by
    simpa only [hg₀, hg₃] using hP
  have hstart : γ₀ 0 ∈ (laneCDoublePrimeWideRect 0).side₁ := by
    rw [hγ₀p.source]
    norm_num [laneCDoublePrimeLongRect, laneCDoublePrimeWideRect,
      MarkedRect.side₁, Complex.mem_reProdIm] at hz₀ ⊢
    exact hz₀
  have hend : γ₁ 1 ∈ (laneCDoublePrimeWideRect 0).side₂ := by
    rw [hγ₁p.target]
    norm_num [laneCDoublePrimeLongRect, laneCDoublePrimeWideRect,
      MarkedRect.side₂, Complex.mem_reProdIm] at hw₁ ⊢
    exact hw₁
  exact ⟨P, hPpiece, hPmap,
    ⟨γ₀ 0, hstart, γ₁ 1, hend, hPpiece, hPwide⟩, hlen⟩

 
end SupercriticalLQGUniqueness.B2.DG20Conc
