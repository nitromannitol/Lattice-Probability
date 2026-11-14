/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSiteExitMeet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBRectMeet
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CCross

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF

 


theorem laneB_siteCirc_meets_top_strip {ξ : ℝ} {f : ℂ → ℝ}
    {b : ℤ × ℤ} {c : ℝ≥0∞} (C : SiteCirc ξ f b c)
    {γ : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hγ : ContinuousOn γ (Icc u v))
    (hbox : ∀ r ∈ Icc u v, γ r ∈ T20D.hatBox 0 b)
    (hstrip : ∀ r ∈ Icc u v, (b.2 : ℝ) + 1 ≤ (γ r).im)
    (hu : (γ u).im = (b.2 : ℝ) + 1)
    (hv : (γ v).im = (b.2 : ℝ) + 2) :
    ∃ r ∈ Icc u v, C.On (γ r) := by
  let x₀ : ℝ := (b.1 : ℝ) - 1
  let x₁ : ℝ := (b.1 : ℝ) + 2
  let y₀ : ℝ := (b.2 : ℝ) + 1
  let y₁ : ℝ := (b.2 : ℝ) + 2
  obtain ⟨z, hz, w, hw, hp, hm⟩ := C.hT
  have hPc : ContinuousOn C.T (Icc (0 : ℝ) 1) := hp.continuousOn
  have hPm : MapsTo C.T (Icc (0 : ℝ) 1) (RectCross.rect x₀ x₁ y₀ y₁) := by
    intro t ht
    have h := mem_toSet_iff.mp (hm t ht)
    simp only [sT] at h
    change (C.T t).re ∈ Icc x₀ x₁ ∧ (C.T t).im ∈ Icc y₀ y₁
    simp only [mem_Icc]
    dsimp [x₀, x₁, y₀, y₁]
    constructor
    · constructor <;> linarith [h.1.1, h.1.2]
    · constructor <;> linarith [h.2.1, h.2.2]
  have hPends : ((C.T 0).re = x₀ ∧ (C.T 1).re = x₁) ∨
      ((C.T 0).re = x₁ ∧ (C.T 1).re = x₀) := by
    left
    rw [hp.source, hp.target]
    simp only [MarkedRect.side₁, MarkedRect.side₂, sT,
      ↓reduceIte, Complex.mem_reProdIm, mem_singleton_iff] at hz hw
    exact ⟨by dsimp [x₀]; exact hz.1, by dsimp [x₁]; linarith [hw.1]⟩
  have h_u : u ∈ Icc u v := ⟨le_rfl, huv⟩
  have h_v : v ∈ Icc u v := ⟨huv, le_rfl⟩
  let Q := Strong.seg γ u v
  have hQc : ContinuousOn Q (Icc (0 : ℝ) 1) :=
    Strong.continuousOn_seg hγ h_u h_v
  have hQm : MapsTo Q (Icc (0 : ℝ) 1) (RectCross.rect x₀ x₁ y₀ y₁) := by
    intro t ht
    have hr := Strong.seg_param_mem h_u h_v ht
    have hb := T20D.mem_hatBox (hbox _ hr)
    have hs := hstrip _ hr
    change (γ (u + t * (v - u))).re ∈ Icc x₀ x₁ ∧
      (γ (u + t * (v - u))).im ∈ Icc y₀ y₁
    simp only [mem_Icc]
    dsimp [x₀, x₁, y₀, y₁]
    exact ⟨⟨by simpa using hb.1, by simpa using hb.2.1⟩,
      hs, by simpa using hb.2.2.2⟩
  have hQends : ((Q 0).im = y₀ ∧ (Q 1).im = y₁) ∨
      ((Q 0).im = y₁ ∧ (Q 1).im = y₀) := by
    left
    simpa only [Q, Strong.seg_zero, Strong.seg_one, y₀, y₁] using And.intro hu hv
  obtain ⟨s, hs, t, ht, he⟩ :=
    laneB_rect_crossings_meet hPc hQc hPm hQm hPends hQends
  let r := u + t * (v - u)
  have hr : r ∈ Icc u v := Strong.seg_param_mem h_u h_v ht
  refine ⟨r, hr, Or.inr (Or.inl ⟨s, hs, ?_⟩)⟩
  simpa only [Q, Strong.seg, r] using he

 
theorem laneB_siteCirc_meets_bottom_strip {ξ : ℝ} {f : ℂ → ℝ}
    {b : ℤ × ℤ} {c : ℝ≥0∞} (C : SiteCirc ξ f b c)
    {γ : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hγ : ContinuousOn γ (Icc u v))
    (hbox : ∀ r ∈ Icc u v, γ r ∈ T20D.hatBox 0 b)
    (hstrip : ∀ r ∈ Icc u v, (γ r).im ≤ (b.2 : ℝ))
    (hu : (γ u).im = (b.2 : ℝ))
    (hv : (γ v).im = (b.2 : ℝ) - 1) :
    ∃ r ∈ Icc u v, C.On (γ r) := by
  let x₀ : ℝ := (b.1 : ℝ) - 1
  let x₁ : ℝ := (b.1 : ℝ) + 2
  let y₀ : ℝ := (b.2 : ℝ) - 1
  let y₁ : ℝ := (b.2 : ℝ)
  obtain ⟨z, hz, w, hw, hp, hm⟩ := C.hB
  have hPc : ContinuousOn C.B (Icc (0 : ℝ) 1) := hp.continuousOn
  have hPm : MapsTo C.B (Icc (0 : ℝ) 1) (RectCross.rect x₀ x₁ y₀ y₁) := by
    intro t ht
    have h := mem_toSet_iff.mp (hm t ht)
    simp only [sB] at h
    change (C.B t).re ∈ Icc x₀ x₁ ∧ (C.B t).im ∈ Icc y₀ y₁
    simp only [mem_Icc]
    dsimp [x₀, x₁, y₀, y₁]
    constructor
    · constructor <;> linarith [h.1.1, h.1.2]
    · constructor <;> linarith [h.2.1, h.2.2]
  have hPends : ((C.B 0).re = x₀ ∧ (C.B 1).re = x₁) ∨
      ((C.B 0).re = x₁ ∧ (C.B 1).re = x₀) := by
    left
    rw [hp.source, hp.target]
    simp only [MarkedRect.side₁, MarkedRect.side₂, sB,
      ↓reduceIte, Complex.mem_reProdIm, mem_singleton_iff] at hz hw
    exact ⟨by dsimp [x₀]; exact hz.1, by dsimp [x₁]; linarith [hw.1]⟩
  have h_u : u ∈ Icc u v := ⟨le_rfl, huv⟩
  have h_v : v ∈ Icc u v := ⟨huv, le_rfl⟩
  let Q := Strong.seg γ u v
  have hQc : ContinuousOn Q (Icc (0 : ℝ) 1) :=
    Strong.continuousOn_seg hγ h_u h_v
  have hQm : MapsTo Q (Icc (0 : ℝ) 1) (RectCross.rect x₀ x₁ y₀ y₁) := by
    intro t ht
    have hr := Strong.seg_param_mem h_u h_v ht
    have hb := T20D.mem_hatBox (hbox _ hr)
    have hs := hstrip _ hr
    change (γ (u + t * (v - u))).re ∈ Icc x₀ x₁ ∧
      (γ (u + t * (v - u))).im ∈ Icc y₀ y₁
    simp only [mem_Icc]
    dsimp [x₀, x₁, y₀, y₁]
    exact ⟨⟨by simpa using hb.1, by simpa using hb.2.1⟩,
      by simpa using hb.2.2.1, hs⟩
  have hQends : ((Q 0).im = y₀ ∧ (Q 1).im = y₁) ∨
      ((Q 0).im = y₁ ∧ (Q 1).im = y₀) := by
    right
    simpa only [Q, Strong.seg_zero, Strong.seg_one, y₀, y₁] using And.intro hu hv
  obtain ⟨s, hs, t, ht, he⟩ :=
    laneB_rect_crossings_meet hPc hQc hPm hQm hPends hQends
  let r := u + t * (v - u)
  have hr : r ∈ Icc u v := Strong.seg_param_mem h_u h_v ht
  refine ⟨r, hr, Or.inl ⟨s, hs, ?_⟩⟩
  simpa only [Q, Strong.seg, r] using he

 
theorem laneB_siteCirc_meets_right_strip {ξ : ℝ} {f : ℂ → ℝ}
    {b : ℤ × ℤ} {c : ℝ≥0∞} (C : SiteCirc ξ f b c)
    {γ : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hγ : ContinuousOn γ (Icc u v))
    (hbox : ∀ r ∈ Icc u v, γ r ∈ T20D.hatBox 0 b)
    (hstrip : ∀ r ∈ Icc u v, (b.1 : ℝ) + 1 ≤ (γ r).re)
    (hu : (γ u).re = (b.1 : ℝ) + 1)
    (hv : (γ v).re = (b.1 : ℝ) + 2) :
    ∃ r ∈ Icc u v, C.On (γ r) := by
  let x₀ : ℝ := (b.1 : ℝ) + 1
  let x₁ : ℝ := (b.1 : ℝ) + 2
  let y₀ : ℝ := (b.2 : ℝ) - 1
  let y₁ : ℝ := (b.2 : ℝ) + 2
  obtain ⟨z, hz, w, hw, hq, hqm⟩ := C.hR
  have hQc : ContinuousOn C.R (Icc (0 : ℝ) 1) := hq.continuousOn
  have hQm : MapsTo C.R (Icc (0 : ℝ) 1) (RectCross.rect x₀ x₁ y₀ y₁) := by
    intro t ht
    have h := mem_toSet_iff.mp (hqm t ht)
    simp only [sR] at h
    change (C.R t).re ∈ Icc x₀ x₁ ∧ (C.R t).im ∈ Icc y₀ y₁
    simp only [mem_Icc]
    dsimp [x₀, x₁, y₀, y₁]
    constructor
    · constructor <;> linarith [h.1.1, h.1.2]
    · constructor <;> linarith [h.2.1, h.2.2]
  have hQends : ((C.R 0).im = y₀ ∧ (C.R 1).im = y₁) ∨
      ((C.R 0).im = y₁ ∧ (C.R 1).im = y₀) := by
    left
    rw [hq.source, hq.target]
    simp [MarkedRect.side₁, MarkedRect.side₂, sR, Complex.mem_reProdIm] at hz hw
    exact ⟨by dsimp [y₀]; exact hz.2, by dsimp [y₁]; linarith [hw.2]⟩
  have h_u : u ∈ Icc u v := ⟨le_rfl, huv⟩
  have h_v : v ∈ Icc u v := ⟨huv, le_rfl⟩
  let P := Strong.seg γ u v
  have hPc : ContinuousOn P (Icc (0 : ℝ) 1) :=
    Strong.continuousOn_seg hγ h_u h_v
  have hPm : MapsTo P (Icc (0 : ℝ) 1) (RectCross.rect x₀ x₁ y₀ y₁) := by
    intro t ht
    have hr := Strong.seg_param_mem h_u h_v ht
    have hb := T20D.mem_hatBox (hbox _ hr)
    have hs := hstrip _ hr
    change (γ (u + t * (v - u))).re ∈ Icc x₀ x₁ ∧
      (γ (u + t * (v - u))).im ∈ Icc y₀ y₁
    simp only [mem_Icc]
    dsimp [x₀, x₁, y₀, y₁]
    exact ⟨⟨hs, by simpa using hb.2.1⟩,
      by simpa using hb.2.2.1, by simpa using hb.2.2.2⟩
  have hPends : ((P 0).re = x₀ ∧ (P 1).re = x₁) ∨
      ((P 0).re = x₁ ∧ (P 1).re = x₀) := by
    left
    simpa only [P, Strong.seg_zero, Strong.seg_one, x₀, x₁] using And.intro hu hv
  obtain ⟨s, hs, t, ht, he⟩ :=
    laneB_rect_crossings_meet hPc hQc hPm hQm hPends hQends
  let r := u + s * (v - u)
  have hr : r ∈ Icc u v := Strong.seg_param_mem h_u h_v hs
  refine ⟨r, hr, Or.inr (Or.inr (Or.inr ⟨t, ht, ?_⟩))⟩
  simpa only [P, Strong.seg, r] using he.symm

 
theorem laneB_siteCirc_meets_left_strip {ξ : ℝ} {f : ℂ → ℝ}
    {b : ℤ × ℤ} {c : ℝ≥0∞} (C : SiteCirc ξ f b c)
    {γ : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hγ : ContinuousOn γ (Icc u v))
    (hbox : ∀ r ∈ Icc u v, γ r ∈ T20D.hatBox 0 b)
    (hstrip : ∀ r ∈ Icc u v, (γ r).re ≤ (b.1 : ℝ))
    (hu : (γ u).re = (b.1 : ℝ))
    (hv : (γ v).re = (b.1 : ℝ) - 1) :
    ∃ r ∈ Icc u v, C.On (γ r) := by
  let x₀ : ℝ := (b.1 : ℝ) - 1
  let x₁ : ℝ := (b.1 : ℝ)
  let y₀ : ℝ := (b.2 : ℝ) - 1
  let y₁ : ℝ := (b.2 : ℝ) + 2
  obtain ⟨z, hz, w, hw, hq, hqm⟩ := C.hL
  have hQc : ContinuousOn C.L (Icc (0 : ℝ) 1) := hq.continuousOn
  have hQm : MapsTo C.L (Icc (0 : ℝ) 1) (RectCross.rect x₀ x₁ y₀ y₁) := by
    intro t ht
    have h := mem_toSet_iff.mp (hqm t ht)
    simp only [sL] at h
    change (C.L t).re ∈ Icc x₀ x₁ ∧ (C.L t).im ∈ Icc y₀ y₁
    simp only [mem_Icc]
    dsimp [x₀, x₁, y₀, y₁]
    constructor
    · constructor <;> linarith [h.1.1, h.1.2]
    · constructor <;> linarith [h.2.1, h.2.2]
  have hQends : ((C.L 0).im = y₀ ∧ (C.L 1).im = y₁) ∨
      ((C.L 0).im = y₁ ∧ (C.L 1).im = y₀) := by
    left
    rw [hq.source, hq.target]
    simp [MarkedRect.side₁, MarkedRect.side₂, sL, Complex.mem_reProdIm] at hz hw
    exact ⟨by dsimp [y₀]; exact hz.2, by dsimp [y₁]; linarith [hw.2]⟩
  have h_u : u ∈ Icc u v := ⟨le_rfl, huv⟩
  have h_v : v ∈ Icc u v := ⟨huv, le_rfl⟩
  let P := Strong.seg γ u v
  have hPc : ContinuousOn P (Icc (0 : ℝ) 1) :=
    Strong.continuousOn_seg hγ h_u h_v
  have hPm : MapsTo P (Icc (0 : ℝ) 1) (RectCross.rect x₀ x₁ y₀ y₁) := by
    intro t ht
    have hr := Strong.seg_param_mem h_u h_v ht
    have hb := T20D.mem_hatBox (hbox _ hr)
    have hs := hstrip _ hr
    change (γ (u + t * (v - u))).re ∈ Icc x₀ x₁ ∧
      (γ (u + t * (v - u))).im ∈ Icc y₀ y₁
    simp only [mem_Icc]
    dsimp [x₀, x₁, y₀, y₁]
    exact ⟨⟨by simpa using hb.1, hs⟩,
      by simpa using hb.2.2.1, by simpa using hb.2.2.2⟩
  have hPends : ((P 0).re = x₀ ∧ (P 1).re = x₁) ∨
      ((P 0).re = x₁ ∧ (P 1).re = x₀) := by
    right
    simpa only [P, Strong.seg_zero, Strong.seg_one, x₀, x₁] using And.intro hu hv
  obtain ⟨s, hs, t, ht, he⟩ :=
    laneB_rect_crossings_meet hPc hQc hPm hQm hPends hQends
  let r := u + s * (v - u)
  have hr : r ∈ Icc u v := Strong.seg_param_mem h_u h_v hs
  refine ⟨r, hr, Or.inr (Or.inr (Or.inl ⟨t, ht, ?_⟩))⟩
  simpa only [P, Strong.seg, r] using he.symm

 


theorem laneB_siteCirc_meets_exit {ξ : ℝ} {f : ℂ → ℝ}
    {b : ℤ × ℤ} {c : ℝ≥0∞} (C : SiteCirc ξ f b c)
    {γ : ℝ → ℂ} {a d : ℝ} (had : a ≤ d)
    (hγ : ContinuousOn γ (Icc a d))
    (hin : γ a ∈ T20.dyBlock 0 b)
    (hout : γ d ∉
      Ioo ((b.1 : ℝ) - 1) ((b.1 : ℝ) + 2) ×ℂ
        Ioo ((b.2 : ℝ) - 1) ((b.2 : ℝ) + 2)) :
    ∃ r ∈ Icc a d, C.On (γ r) := by
  let x₀ : ℝ := (b.1 : ℝ) - 1
  let x₁ : ℝ := (b.1 : ℝ)
  let x₂ : ℝ := (b.1 : ℝ) + 1
  let x₃ : ℝ := (b.1 : ℝ) + 2
  let y₀ : ℝ := (b.2 : ℝ) - 1
  let y₁ : ℝ := (b.2 : ℝ)
  let y₂ : ℝ := (b.2 : ℝ) + 1
  let y₃ : ℝ := (b.2 : ℝ) + 2
  have hin' : γ a ∈ Icc x₁ x₂ ×ℂ Icc y₁ y₂ := by
    simpa [T20.dyBlock, x₁, x₂, y₁, y₂] using hin
  have hout' : γ d ∉ Ioo x₀ x₃ ×ℂ Ioo y₀ y₃ := by
    simpa only [x₀, x₃, y₀, y₃] using hout
  obtain ⟨u, v, hau, huv, hvd, hbox, hcase⟩ :=
    T20C.annulus_cross had hγ
      (show x₀ < x₁ by dsimp [x₀, x₁]; linarith)
      (show x₂ < x₃ by dsimp [x₂, x₃]; linarith)
      (show y₀ < y₁ by dsimp [y₀, y₁]; linarith)
      (show y₂ < y₃ by dsimp [y₂, y₃]; linarith)
      hin' hout'
  have hsub : Icc u v ⊆ Icc a d := Icc_subset_Icc hau hvd
  have hγ' : ContinuousOn γ (Icc u v) := hγ.mono hsub
  have hbox' : ∀ r ∈ Icc u v, γ r ∈ T20D.hatBox 0 b := by
    intro r hr
    have h := hbox r hr
    simpa [T20D.hatBox, x₀, x₃, y₀, y₃] using h
  rcases hcase with hT | hB | hR | hL
  · obtain ⟨r, hr, hmeet⟩ := laneB_siteCirc_meets_top_strip C huv.le hγ' hbox'
        (by intro s hs; have := hT.2.2 s hs; simpa only [y₂] using this)
        (by simpa only [y₂] using hT.1)
        (by simpa only [y₃] using hT.2.1)
    exact ⟨r, hsub hr, hmeet⟩
  · obtain ⟨r, hr, hmeet⟩ := laneB_siteCirc_meets_bottom_strip C huv.le hγ' hbox'
        (by intro s hs; have := hB.2.2 s hs; simpa only [y₁] using this)
        (by simpa only [y₁] using hB.1)
        (by simpa only [y₀] using hB.2.1)
    exact ⟨r, hsub hr, hmeet⟩
  · obtain ⟨r, hr, hmeet⟩ := laneB_siteCirc_meets_right_strip C huv.le hγ' hbox'
        (by intro s hs; have := hR.2.2 s hs; simpa only [x₂] using this)
        (by simpa only [x₂] using hR.1)
        (by simpa only [x₃] using hR.2.1)
    exact ⟨r, hsub hr, hmeet⟩
  · obtain ⟨r, hr, hmeet⟩ := laneB_siteCirc_meets_left_strip C huv.le hγ' hbox'
        (by intro s hs; have := hL.2.2 s hs; simpa only [x₁] using this)
        (by simpa only [x₁] using hL.1)
        (by simpa only [x₀] using hL.2.1)
    exact ⟨r, hsub hr, hmeet⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
