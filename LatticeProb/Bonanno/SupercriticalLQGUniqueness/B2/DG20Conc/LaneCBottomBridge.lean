/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCBottomBridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCBridgeGeneric
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCBottomConnector
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCDoublePrimeWide

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

theorem laneC_bottom_side_bridge_wide {ξ : ℝ} {f : ℂ → ℝ}
    {γ₀ γ₁ δ : ℝ → ℂ}
    (hγ₀ : AdmPath (laneCDoublePrimeLongRect 2).toSet
      (laneCDoublePrimeLongRect 2).side₁
      (laneCDoublePrimeLongRect 2).side₂ γ₀)
    (hγ₁ : AdmPath (laneCDoublePrimeLongRect 3).toSet
      (laneCDoublePrimeLongRect 3).side₁
      (laneCDoublePrimeLongRect 3).side₂ γ₁)
    (hδ : AdmPath laneCBottomConnector.toSet
      laneCBottomConnector.side₁ laneCBottomConnector.side₂ δ) :
    ∃ P : ℝ → ℂ,
      AdmPath (laneCDoublePrimeWideRect 1).toSet
        (laneCDoublePrimeWideRect 1).side₁
        (laneCDoublePrimeWideRect 1).side₂ P ∧
      lfppLen ξ f P ≤ lfppLen ξ f γ₀ + lfppLen ξ f δ + lfppLen ξ f γ₁ := by
  obtain ⟨a, b, ha, hab, hb, hδring,
    ⟨s₀, hs₀, t₀, ht₀, m₀⟩, ⟨s₁, hs₁, t₁, ht₁, m₁⟩⟩ :=
    laneC_bottom_connector_meets_both hγ₀ hγ₁ hδ
  obtain ⟨z₀, hz₀, w₀, hw₀, hγ₀p, hγ₀map⟩ := hγ₀
  obtain ⟨z₁, hz₁, w₁, hw₁, hγ₁p, hγ₁map⟩ := hγ₁
  obtain ⟨zd, hzd, wd, hwd, hδp, hδmap⟩ := hδ
  let δ' := subPath δ a b
  have hγ₀p' : IsPiecewiseC1Path γ₀ (γ₀ 0) (γ₀ 1) := by
    simpa only [hγ₀p.source, hγ₀p.target] using hγ₀p
  have hγ₁p' : IsPiecewiseC1Path γ₁ (γ₁ 0) (γ₁ 1) := by
    simpa only [hγ₁p.source, hγ₁p.target] using hγ₁p
  have hδp' : IsPiecewiseC1Path δ' (δ' 0) (δ' 1) := by
    convert isPiecewiseC1Path_subPath hδp ha hab hb using 1 <;>
      simp [δ', subPath]
  have hbottom₀ : MapsTo γ₀ (Icc (0 : ℝ) 1)
      (laneCDoublePrimeWideRect 1).toSet := by
    intro t ht
    have h := hγ₀map t ht
    norm_num [laneCDoublePrimeLongRect, laneCDoublePrimeWideRect,
      MarkedRect.toSet, Complex.mem_reProdIm] at h ⊢
    exact ⟨⟨h.1.1, by linarith [h.1.2]⟩, h.2⟩
  have hbottom₁ : MapsTo γ₁ (Icc (0 : ℝ) 1)
      (laneCDoublePrimeWideRect 1).toSet := by
    intro t ht
    have h := hγ₁map t ht
    norm_num [laneCDoublePrimeLongRect, laneCDoublePrimeWideRect,
      MarkedRect.toSet, Complex.mem_reProdIm] at h ⊢
    exact ⟨⟨by linarith [h.1.1], h.1.2⟩, h.2⟩
  have hbottomδ : MapsTo δ' (Icc (0 : ℝ) 1)
      (laneCDoublePrimeWideRect 1).toSet := by
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
    norm_num [laneCBottomConnector, MarkedRect.toSet,
      Complex.mem_reProdIm] at hfull
    simp only [laneCOuterCluster, Complex.mem_reProdIm, mem_Icc] at houter
    dsimp [δ', subPath] at hnot houter
    have hyle : (δ' t).im ≤ -1 := by
      by_contra h
      dsimp [δ', subPath] at h
      apply hnot
      exact ⟨⟨by linarith [hfull.1.1], by linarith [hfull.1.2]⟩,
        ⟨by linarith [hfull.2.1], by linarith⟩⟩
    norm_num [laneCDoublePrimeWideRect, MarkedRect.toSet,
      Complex.mem_reProdIm]
    dsimp [δ', subPath]
    exact ⟨⟨by linarith [hfull.1.1], by linarith [hfull.1.2]⟩,
      ⟨by linarith [houter.2.1], hyle⟩⟩
  have hstart : γ₀ 0 ∈ (laneCDoublePrimeWideRect 1).side₁ := by
    rw [hγ₀p.source]
    norm_num [laneCDoublePrimeLongRect, laneCDoublePrimeWideRect,
      MarkedRect.side₁, Complex.mem_reProdIm] at hz₀ ⊢
    exact hz₀
  have hend : γ₁ 1 ∈ (laneCDoublePrimeWideRect 1).side₂ := by
    rw [hγ₁p.target]
    norm_num [laneCDoublePrimeLongRect, laneCDoublePrimeWideRect,
      MarkedRect.side₂, Complex.mem_reProdIm] at hw₁ ⊢
    exact hw₁
  obtain ⟨P, hP, hcost⟩ := laneC_three_crossing_bridge
    hγ₀p' hγ₁p' hδp' hbottom₀ hbottom₁ hbottomδ hstart hend
    hs₀ ht₀ hs₁ ht₁ m₀ m₁
  refine ⟨P, hP, hcost.trans ?_⟩
  have hδlen : lfppLen ξ f δ' ≤ lfppLen ξ f δ :=
    laneC_subpath_len_le ha hab hb
  exact add_le_add (add_le_add le_rfl hδlen) le_rfl

end SupercriticalLQGUniqueness.B2.DG20Conc
