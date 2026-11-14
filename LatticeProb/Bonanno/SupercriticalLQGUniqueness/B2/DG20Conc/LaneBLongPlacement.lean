/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBLongPlacement at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBBoundaryFamily
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S1Geom

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

private theorem laneB_sB_subset_hatBox (b : ℤ × ℤ) :
    (sB b).toSet ⊆ T20D.hatBox 0 b := by
  intro z hz
  simp only [sB, MarkedRect.toSet, T20D.hatBox, pow_zero, mul_one,
    Complex.mem_reProdIm, mem_Icc] at hz ⊢
  rcases hz with ⟨⟨h1, h2⟩, h3, h4⟩
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

private theorem laneB_sT_subset_hatBox (b : ℤ × ℤ) :
    (sT b).toSet ⊆ T20D.hatBox 0 b := by
  intro z hz
  simp only [sT, MarkedRect.toSet, T20D.hatBox, pow_zero, mul_one,
    Complex.mem_reProdIm, mem_Icc] at hz ⊢
  rcases hz with ⟨⟨h1, h2⟩, h3, h4⟩
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

private theorem laneB_sL_subset_hatBox (b : ℤ × ℤ) :
    (sL b).toSet ⊆ T20D.hatBox 0 b := by
  intro z hz
  simp only [sL, MarkedRect.toSet, T20D.hatBox, pow_zero, mul_one,
    Complex.mem_reProdIm, mem_Icc] at hz ⊢
  rcases hz with ⟨⟨h1, h2⟩, h3, h4⟩
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

private theorem laneB_sR_subset_hatBox (b : ℤ × ℤ) :
    (sR b).toSet ⊆ T20D.hatBox 0 b := by
  intro z hz
  simp only [sR, MarkedRect.toSet, T20D.hatBox, pow_zero, mul_one,
    Complex.mem_reProdIm, mem_Icc] at hz ⊢
  rcases hz with ⟨⟨h1, h2⟩, h3, h4⟩
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

 

theorem laneB_siteCirc_sub_open_annulus
    {R : ℝ} (hR : 24 ≤ R) {b : ℤ × ℤ}
    (hb : b ∈ laneBBoundaryBlocks (laneBGridRadius R)) :
    SiteCirc.Sub {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R} b := by
  have hhat := laneB_boundary_hatBox_subset_open_annulus hR hb
  exact ⟨(laneB_sB_subset_hatBox b).trans hhat,
    (laneB_sT_subset_hatBox b).trans hhat,
    (laneB_sL_subset_hatBox b).trans hhat,
    (laneB_sR_subset_hatBox b).trans hhat⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
