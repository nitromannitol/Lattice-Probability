/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSmallAnnulusGeometry at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAnnuli
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBPhiOscGaussianEvent

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

 

theorem laneB_unit_small_annuli_subset_outer_cluster (i : Bool) :
    laneCUnitUcross i ⊆ laneCOuterCluster := by
  cases i
  · intro z hz
    have hz' : z ∈ cthickening 1 laneCUnitBlock :=
      (closure_thickening_subset_cthickening 1 laneCUnitBlock)
        ((closure_mono sdiff_subset) hz)
    have hc := (rectAB 1 1).isCompact_toSet
    change z ∈ cthickening 1 (rectAB 1 1).toSet at hz'
    rw [hc.cthickening_eq_biUnion_closedBall (by norm_num)] at hz'
    simp only [mem_iUnion] at hz'
    obtain ⟨s, hs, hzs⟩ := hz'
    rw [mem_closedBall, dist_eq_norm] at hzs
    simp only [MarkedRect.toSet, rectAB, Complex.mem_reProdIm,
      mem_Icc, zero_add] at hs
    have hre := (Complex.abs_re_le_norm (z - s)).trans hzs
    have him := (Complex.abs_im_le_norm (z - s)).trans hzs
    rw [Complex.sub_re, abs_le] at hre
    rw [Complex.sub_im, abs_le] at him
    simp only [laneCOuterCluster, Complex.mem_reProdIm, mem_Icc]
    exact ⟨⟨by linarith [hre.1, hs.1.1], by linarith [hre.2, hs.1.2]⟩,
      by linarith [him.1, hs.2.1], by linarith [him.2, hs.2.2]⟩
  · intro z hz
    exact hz.1

 

theorem laneB_unit_small_annuli_radius (i : Bool)
    {z : ℂ} (hz : z ∈ laneCUnitUcross i) :
    ‖z - (⟨1 / 2, 1 / 2⟩ : ℂ)‖ ≤ 5 := by
  have h := laneB_unit_small_annuli_subset_outer_cluster i hz
  simp only [laneCOuterCluster, Complex.mem_reProdIm, mem_Icc] at h
  have hr : |(z - (⟨1 / 2, 1 / 2⟩ : ℂ)).re| ≤ 5 / 2 := by
    rw [Complex.sub_re, abs_le]
    change -(5 / 2 : ℝ) ≤ z.re - 1 / 2 ∧ z.re - 1 / 2 ≤ 5 / 2
    constructor <;> linarith [h.1.1, h.1.2]
  have hi : |(z - (⟨1 / 2, 1 / 2⟩ : ℂ)).im| ≤ 5 / 2 := by
    rw [Complex.sub_im, abs_le]
    change -(5 / 2 : ℝ) ≤ z.im - 1 / 2 ∧ z.im - 1 / 2 ≤ 5 / 2
    constructor <;> linarith [h.2.1, h.2.2]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

end SupercriticalLQGUniqueness.B2.DG20Conc
