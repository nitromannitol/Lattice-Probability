/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.SquareCrossStrip at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P16Indep

 


set_option autoImplicit false
noncomputable section

open Set
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem rectLen_unit_le_crossLenIn_strip (ξ : ℝ) (f : ℂ → ℝ)
    (U A B : Set ℂ)
    (hU : ∀ z ∈ U, z.im ∈ Icc (0 : ℝ) 1)
    (hA : ∀ z ∈ A, z.re ≤ 0)
    (hB : ∀ z ∈ B, 1 ≤ z.re) :
    rectLen ξ f (rectAB 1 1) ≤ crossLenIn ξ f U A B := by
  refine le_crossLenIn fun P hP => ?_
  obtain ⟨z, hz, w, hw, hPc, hPU⟩ := hP
  obtain ⟨s, t, h0s, hst, ht1, hfs, hft, hI⟩ := RectCross.exists_sub_crossing
    (f := fun u => (P u).re) zero_le_one
    (Complex.continuous_re.comp_continuousOn hPc.continuousOn)
    (by norm_num : (0 : ℝ) ≤ 1)
    (show (P 0).re ≤ 0 by rw [hPc.source]; exact hA z hz)
    (show 1 ≤ (P 1).re by rw [hPc.target]; exact hB w hw)
  have hs : s ∈ Icc (0 : ℝ) 1 := ⟨h0s, hst.trans ht1⟩
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨h0s.trans hst, ht1⟩
  refine crossLenIn_le_of_sub hPc hs ht (fun u hu => ?_) ?_ ?_
  · rw [uIcc_of_le hst] at hu
    rw [mem_rectAB_toSet]
    exact ⟨hI u hu, hU (P u) (hPU u ⟨h0s.trans hu.1, hu.2.trans ht1⟩)⟩
  · rw [mem_rectAB_side₁]
    exact ⟨hfs, hU (P s) (hPU s hs)⟩
  · rw [mem_rectAB_side₂]
    exact ⟨hft, hU (P t) (hPU t ht)⟩

 

theorem crossLenIn_le_rectLen_unit (ξ : ℝ) (f : ℂ → ℝ)
    (U A B : Set ℂ)
    (hU : (rectAB 1 1).toSet ⊆ U)
    (hA : (rectAB 1 1).side₁ ⊆ A)
    (hB : (rectAB 1 1).side₂ ⊆ B) :
    crossLenIn ξ f U A B ≤ rectLen ξ f (rectAB 1 1) := by
  refine le_crossLenIn fun P hP => ?_
  obtain ⟨z, hz, w, hw, hPc, hPU⟩ := hP
  exact crossLenIn_le_lfppLen
    ⟨z, hA hz, w, hB hw, hPc, fun t ht => hU (hPU t ht)⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
