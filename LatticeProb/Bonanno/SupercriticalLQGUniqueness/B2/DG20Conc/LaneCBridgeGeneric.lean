/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCBridgeGeneric at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeHorizontalClip
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeTopClip
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCGlue4LFPP

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

theorem laneC_bridge_two_paths {ξ : ℝ} {f : ℂ → ℝ}
    {U E F : Set ℂ} {p q d : ℝ → ℂ}
    (hp : IsPiecewiseC1Path p (p 0) (p 1))
    (hq : IsPiecewiseC1Path q (q 0) (q 1))
    (hd : IsPiecewiseC1Path d (d 0) (d 1))
    (hpU : MapsTo p (Icc (0 : ℝ) 1) U)
    (hqU : MapsTo q (Icc (0 : ℝ) 1) U)
    (hdU : MapsTo d (Icc (0 : ℝ) 1) U)
    (hE : p 0 ∈ E) (hF : q 1 ∈ F)
    (hpd : ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, p s = d t)
    (hqd : ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, q s = d t) :
    ∃ r : ℝ → ℂ, AdmPath U E F r ∧
      lfppLen ξ f r ≤ lfppLen ξ f p + lfppLen ξ f d + lfppLen ξ f q := by
  obtain ⟨s₀, hs₀, t₀, ht₀, e₀⟩ := hpd
  obtain ⟨s₁, hs₁, t₁, ht₁, e₁⟩ := hqd
  let g₀ := Strong.seg p 0 s₀
  let g₁ := Strong.seg d t₀ t₁
  let g₂ := Strong.seg q s₁ 1
  let g₃ : ℝ → ℂ := fun _ => q 1
  let r := laneCConcat4 g₀ g₁ g₂ g₃
  have h01 : g₀ 1 = g₁ 0 := by simpa [g₀, g₁] using e₀
  have h12 : g₁ 1 = g₂ 0 := by simpa [g₁, g₂] using e₁.symm
  have h23 : g₂ 1 = g₃ 0 := by simp [g₂, g₃]
  have hg₀ : IsPiecewiseC1Path g₀ (g₀ 0) (g₀ 1) := by
    simpa [g₀] using laneC_strong_seg_piecewise hp
      (by norm_num : (0 : ℝ) ∈ Icc 0 1) hs₀
  have hg₁ : IsPiecewiseC1Path g₁ (g₁ 0) (g₁ 1) := by
    simpa [g₁] using laneC_strong_seg_piecewise hd ht₀ ht₁
  have hg₂ : IsPiecewiseC1Path g₂ (g₂ 0) (g₂ 1) := by
    simpa [g₂] using laneC_strong_seg_piecewise hq hs₁
      (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  have hg₃ : IsPiecewiseC1Path g₃ (g₃ 0) (g₃ 1) := by
    simpa [g₃] using LQGMetric.DDDF.isPiecewiseC1Path_const (q 1)
  have hrp : IsPiecewiseC1Path r (p 0) (q 1) := by
    have hp' : IsPiecewiseC1Path r (g₀ 0) (g₃ 1) :=
      laneC_concat4_piecewise hg₀
        (by simpa only [h01] using hg₁)
        (by simpa only [h12] using hg₂)
        (by simpa only [h23] using hg₃)
    simpa [r, laneCConcat4, concatPath, g₀, g₃, Strong.seg] using hp'
  have hrU : MapsTo r (Icc (0 : ℝ) 1) U := by
    apply laneC_concat4_mapsTo
    · exact Strong.mapsTo_seg hpU (by norm_num) hs₀
    · exact Strong.mapsTo_seg hdU ht₀ ht₁
    · exact Strong.mapsTo_seg hqU hs₁ (by norm_num)
    · intro t ht
      exact hqU (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  have hlen : lfppLen ξ f r ≤ lfppLen ξ f p + lfppLen ξ f d +
      lfppLen ξ f q := by
    rw [laneC_concat4_length h01 h12 h23]
    have h₀ := laneC_strong_seg_len_le (ξ := ξ) (f := f) p
      (by norm_num : (0 : ℝ) ∈ Icc 0 1) hs₀
    have h₁ := laneC_strong_seg_len_le (ξ := ξ) (f := f) d ht₀ ht₁
    have h₂ := laneC_strong_seg_len_le (ξ := ξ) (f := f) q hs₁
      (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    rw [show lfppLen ξ f g₃ = 0 by exact LQGMetric.DDDF.lfppLen_const _]
    simpa only [add_zero] using add_le_add (add_le_add h₀ h₁) h₂
  refine ⟨r, ?_, hlen⟩
  have hsource : r 0 = p 0 := by norm_num [r, laneCConcat4, concatPath, g₀, Strong.seg]
  have htarget : r 1 = q 1 := by norm_num [r, laneCConcat4, concatPath, g₃]
  exact ⟨p 0, hE, q 1, hF, by simpa [hsource, htarget] using hrp, hrU⟩

 


theorem laneC_three_crossing_bridge {ξ : ℝ} {f : ℂ → ℝ}
    {U A B : Set ℂ} {γ₀ γ₁ δ : ℝ → ℂ}
    (hγ₀ : IsPiecewiseC1Path γ₀ (γ₀ 0) (γ₀ 1))
    (hγ₁ : IsPiecewiseC1Path γ₁ (γ₁ 0) (γ₁ 1))
    (hδ : IsPiecewiseC1Path δ (δ 0) (δ 1))
    (hmap₀ : MapsTo γ₀ (Icc (0 : ℝ) 1) U)
    (hmap₁ : MapsTo γ₁ (Icc (0 : ℝ) 1) U)
    (hmapδ : MapsTo δ (Icc (0 : ℝ) 1) U)
    (hstart : γ₀ 0 ∈ A) (hend : γ₁ 1 ∈ B)
    {s₀ t₀ s₁ t₁ : ℝ}
    (hs₀ : s₀ ∈ Icc (0 : ℝ) 1) (ht₀ : t₀ ∈ Icc (0 : ℝ) 1)
    (hs₁ : s₁ ∈ Icc (0 : ℝ) 1) (ht₁ : t₁ ∈ Icc (0 : ℝ) 1)
    (hm₀ : γ₀ s₀ = δ t₀) (hm₁ : γ₁ s₁ = δ t₁) :
    ∃ P : ℝ → ℂ, AdmPath U A B P ∧
      lfppLen ξ f P ≤ lfppLen ξ f γ₀ + lfppLen ξ f δ + lfppLen ξ f γ₁ :=
  laneC_bridge_two_paths hγ₀ hγ₁ hδ hmap₀ hmap₁ hmapδ hstart hend
    ⟨s₀, hs₀, t₀, ht₀, hm₀⟩ ⟨s₁, hs₁, t₁, ht₁, hm₁⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
