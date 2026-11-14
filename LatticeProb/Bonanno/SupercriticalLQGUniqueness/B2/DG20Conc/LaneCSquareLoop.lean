/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSquareLoop at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSquareWinding
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCGlue4LFPP
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCDoublePrimeWide
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPushDegree

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set QuantumZipper.CA.Topo

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

 


theorem laneC_four_wide_closed_loop {ξ : ℝ} {f : ℂ → ℝ}
    {top bot left right : ℝ → ℂ}
    (htop : AdmPath (laneCDoublePrimeWideRect 0).toSet
      (laneCDoublePrimeWideRect 0).side₁
      (laneCDoublePrimeWideRect 0).side₂ top)
    (hbot : AdmPath (laneCDoublePrimeWideRect 1).toSet
      (laneCDoublePrimeWideRect 1).side₁
      (laneCDoublePrimeWideRect 1).side₂ bot)
    (hleft : AdmPath (laneCDoublePrimeWideRect 2).toSet
      (laneCDoublePrimeWideRect 2).side₁
      (laneCDoublePrimeWideRect 2).side₂ left)
    (hright : AdmPath (laneCDoublePrimeWideRect 3).toSet
      (laneCDoublePrimeWideRect 3).side₁
      (laneCDoublePrimeWideRect 3).side₂ right) :
    ∃ γ : ℝ → ℂ,
      ∃ hp : IsPiecewiseC1Path γ (γ 0) (γ 1),
      ∃ _hc : γ 0 = γ 1,
      ∃ hm : MapsTo γ (Icc (0 : ℝ) 1) laneCDoublePrimeCross,
      loopDeg
        ⟨fun u : unitInterval => γ u - laneCSquareCenter,
          (hp.continuousOn.comp_continuous continuous_subtype_val
            (fun u => u.2)).sub continuous_const⟩
        (by
          intro u hz
          have hn := laneC_closed_ring_norm_ge (hm u.2)
          rw [show γ u - laneCSquareCenter = 0 from hz, norm_zero] at hn
          norm_num at hn) = 1 ∧
      lfppLen ξ f γ ≤ lfppLen ξ f top + lfppLen ξ f bot +
        lfppLen ξ f left + lfppLen ξ f right := by
  obtain ⟨sTL, hsTL, tTL, htTL, eTL⟩ :=
    (laneC_double_prime_wide_corners htop hbot hleft hright).1
  obtain ⟨sTR, hsTR, tTR, htTR, eTR⟩ :=
    (laneC_double_prime_wide_corners htop hbot hleft hright).2.1
  obtain ⟨sBL, hsBL, tBL, htBL, eBL⟩ :=
    (laneC_double_prime_wide_corners htop hbot hleft hright).2.2.1
  obtain ⟨sBR, hsBR, tBR, htBR, eBR⟩ :=
    (laneC_double_prime_wide_corners htop hbot hleft hright).2.2.2
  obtain ⟨_, _, _, _, htp, htm⟩ := htop
  obtain ⟨_, _, _, _, hbp, hbm⟩ := hbot
  obtain ⟨_, _, _, _, hlp, hlm⟩ := hleft
  obtain ⟨_, _, _, _, hrp, hrm⟩ := hright
  let g₀ := Strong.seg top sTR sTL
  let g₁ := Strong.seg left tTL tBL
  let g₂ := Strong.seg bot sBL sBR
  let g₃ := Strong.seg right tBR tTR
  have h01 : g₀ 1 = g₁ 0 := by simpa [g₀, g₁] using eTL
  have h12 : g₁ 1 = g₂ 0 := by simpa [g₁, g₂] using eBL.symm
  have h23 : g₂ 1 = g₃ 0 := by simpa [g₂, g₃] using eBR
  have h30 : g₃ 1 = g₀ 0 := by simpa [g₃, g₀] using eTR.symm
  have hp₀ := laneC_strong_seg_piecewise htp hsTR hsTL
  have hp₁ := laneC_strong_seg_piecewise hlp htTL htBL
  have hp₂ := laneC_strong_seg_piecewise hbp hsBL hsBR
  have hp₃ := laneC_strong_seg_piecewise hrp htBR htTR
  have hm₀ : MapsTo g₀ (Icc (0 : ℝ) 1) (laneCDoublePrimeWideRect 0).toSet :=
    Strong.mapsTo_seg htm hsTR hsTL
  have hm₁ : MapsTo g₁ (Icc (0 : ℝ) 1) (laneCDoublePrimeWideRect 2).toSet :=
    Strong.mapsTo_seg hlm htTL htBL
  have hm₂ : MapsTo g₂ (Icc (0 : ℝ) 1) (laneCDoublePrimeWideRect 1).toSet :=
    Strong.mapsTo_seg hbm hsBL hsBR
  have hm₃ : MapsTo g₃ (Icc (0 : ℝ) 1) (laneCDoublePrimeWideRect 3).toSet :=
    Strong.mapsTo_seg hrm htBR htTR
  have hupper : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (g₀ t - laneCSquareCenter).im := by
    intro t ht
    have h := hm₀ ht
    norm_num [laneCDoublePrimeWideRect, MarkedRect.toSet,
      Complex.mem_reProdIm] at h
    simp only [Complex.sub_im, laneCSquareCenter] at *
    linarith [h.2.1]
  have hleft : ∀ t ∈ Icc (0 : ℝ) 1, (g₁ t - laneCSquareCenter).re < 0 := by
    intro t ht
    have h := hm₁ ht
    norm_num [laneCDoublePrimeWideRect, MarkedRect.toSet,
      Complex.mem_reProdIm] at h
    simp only [Complex.sub_re, laneCSquareCenter] at *
    linarith [h.1.2]
  have hbottom : ∀ t ∈ Icc (0 : ℝ) 1, (g₂ t - laneCSquareCenter).im < 0 := by
    intro t ht
    have h := hm₂ ht
    norm_num [laneCDoublePrimeWideRect, MarkedRect.toSet,
      Complex.mem_reProdIm] at h
    simp only [Complex.sub_im, laneCSquareCenter] at *
    linarith [h.2.2]
  have hright : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (g₃ t - laneCSquareCenter).re := by
    intro t ht
    have h := hm₃ ht
    norm_num [laneCDoublePrimeWideRect, MarkedRect.toSet,
      Complex.mem_reProdIm] at h
    simp only [Complex.sub_re, laneCSquareCenter] at *
    linarith [h.1.1]
  let γ := laneCConcat4 g₀ g₁ g₂ g₃
  have hγ0 : γ 0 = g₀ 0 := by norm_num [γ, laneCConcat4, concatPath]
  have hγ1 : γ 1 = g₃ 1 := by norm_num [γ, laneCConcat4, concatPath]
  have hp : IsPiecewiseC1Path γ (γ 0) (γ 1) := by
    have hp₁' : IsPiecewiseC1Path g₁ (g₀ 1) (g₁ 1) := by
      rw [h01]
      simpa [g₁] using hp₁
    have hp₂' : IsPiecewiseC1Path g₂ (g₁ 1) (g₂ 1) := by
      rw [h12]
      simpa [g₂] using hp₂
    have hp₃' : IsPiecewiseC1Path g₃ (g₂ 1) (g₃ 1) := by
      rw [h23]
      simpa [g₃] using hp₃
    have hp₀' : IsPiecewiseC1Path g₀ (g₀ 0) (g₀ 1) := by
      simpa [g₀] using hp₀
    have h : IsPiecewiseC1Path γ (g₀ 0) (g₃ 1) :=
      laneC_concat4_piecewise hp₀' hp₁' hp₂' hp₃'
    rwa [hγ0, hγ1]
  have hc : γ 0 = γ 1 := by
    rw [hγ0, hγ1]
    exact h30.symm
  have hm : MapsTo γ (Icc (0 : ℝ) 1) laneCDoublePrimeCross :=
    laneC_concat4_mapsTo
      (fun t ht => laneC_double_prime_wide_rect_subset 0 (hm₀ ht))
      (fun t ht => laneC_double_prime_wide_rect_subset 2 (hm₁ ht))
      (fun t ht => laneC_double_prime_wide_rect_subset 1 (hm₂ ht))
      (fun t ht => laneC_double_prime_wide_rect_subset 3 (hm₃ ht))
  have hstrong := laneC_four_side_winding laneCSquareCenter g₀ g₁ g₂ g₃
    hp₀.continuousOn hp₁.continuousOn hp₂.continuousOn hp₃.continuousOn
    hupper hleft hbottom hright h01 h12 h23 h30
  have hγdeg : loopDeg
      ⟨fun u : unitInterval => γ u - laneCSquareCenter,
        (hp.continuousOn.comp_continuous continuous_subtype_val
          (fun u => u.2)).sub continuous_const⟩
      (by
        intro u hz
        have hn := laneC_closed_ring_norm_ge (hm u.2)
        rw [show γ u - laneCSquareCenter = 0 from hz, norm_zero] at hn
        norm_num at hn) = 1 := by
    convert hstrong using 1
    congr 1
    ext u
    exact congrArg (fun z : ℂ => z - laneCSquareCenter)
      (laneC_concat4_eq_strong_glue4 g₀ g₁ g₂ g₃ u.2)
  have hlen : lfppLen ξ f γ ≤ lfppLen ξ f top + lfppLen ξ f bot +
      lfppLen ξ f left + lfppLen ξ f right := by
    rw [show lfppLen ξ f γ = lfppLen ξ f g₀ + lfppLen ξ f g₁ +
      lfppLen ξ f g₂ + lfppLen ξ f g₃ from laneC_concat4_length h01 h12 h23]
    have h₀ := laneC_strong_seg_len_le (ξ := ξ) (f := f) top hsTR hsTL
    have h₁ := laneC_strong_seg_len_le (ξ := ξ) (f := f) left htTL htBL
    have h₂ := laneC_strong_seg_len_le (ξ := ξ) (f := f) bot hsBL hsBR
    have h₃ := laneC_strong_seg_len_le (ξ := ξ) (f := f) right htBR htTR
    exact (add_le_add (add_le_add (add_le_add h₀ h₁) h₂) h₃).trans_eq (by ac_rfl)
  exact ⟨γ, hp, hc, hm, hγdeg, hlen⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
