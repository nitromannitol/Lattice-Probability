/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCShortHit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCShortGrid

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

 

theorem laneC_crossing_hits_half_dist (S : Set ℂ) {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hstart : Metric.infDist (γ 0) S = 0)
    (hend : 1 ≤ Metric.infDist (γ 1) S) :
    ∃ t ∈ Icc (0 : ℝ) 1, Metric.infDist (γ t) S = 1 / 2 := by
  have hcont : ContinuousOn (fun t => Metric.infDist (γ t) S) (Icc (0 : ℝ) 1) :=
    (Metric.continuous_infDist_pt (s := S)).comp_continuousOn hγ
  obtain ⟨t, ht, hval⟩ :=
    intermediate_value_Icc zero_le_one hcont
      (show (1 / 2 : ℝ) ∈ Icc (Metric.infDist (γ 0) S)
          (Metric.infDist (γ 1) S) from by
        simp only [mem_Icc]
        constructor <;> linarith)
  exact ⟨t, ht, hval⟩

 
theorem laneC_prime_inner_infDist_zero {z : ℂ} (hz : z ∈ laneCPrimeInner) :
    Metric.infDist z laneCUnitBlock = 0 := by
  have hclosed : IsClosed laneCUnitBlock :=
    (rectAB 1 1).isCompact_toSet.isClosed
  have hmem : z ∈ laneCUnitBlock :=
    hclosed.closure_eq ▸ frontier_subset_closure hz
  exact Metric.infDist_zero_of_mem hmem

 

theorem laneC_prime_outer_infDist_one {z : ℂ} (hz : z ∈ laneCPrimeOuter) :
    Metric.infDist z laneCUnitBlock = 1 := by
  have h := Metric.frontier_thickening_subset laneCUnitBlock hz
  simpa [Metric.infDist] using congrArg ENNReal.toReal h

 

theorem laneC_double_prime_inner_infDist_zero {z : ℂ}
    (hz : z ∈ laneCDoublePrimeInner) :
    Metric.infDist z laneCInnerCluster = 0 := by
  have hclosed : IsClosed laneCInnerCluster :=
    isClosed_Icc.reProdIm isClosed_Icc
  have hmem : z ∈ laneCInnerCluster :=
    hclosed.closure_eq ▸ frontier_subset_closure hz
  exact Metric.infDist_zero_of_mem hmem

 

theorem laneC_double_prime_outer_infDist_ge_one {z : ℂ}
    (hz : z ∈ laneCDoublePrimeOuter) :
    1 ≤ Metric.infDist z laneCInnerCluster := by
  have hne : laneCInnerCluster.Nonempty := by
    refine ⟨0, ?_⟩
    simp [laneCInnerCluster, Complex.mem_reProdIm]
  apply (Metric.le_infDist hne).mpr
  intro w hw
  have hw' : -1 ≤ w.re ∧ w.re ≤ 2 ∧ -1 ≤ w.im ∧ w.im ≤ 2 := by
    simpa [laneCInnerCluster, Complex.mem_reProdIm, mem_Icc, and_assoc] using hw
  have hz' : z.im = -2 ∨ z.im = 3 ∨ z.re = -2 ∨ z.re = 3 := by
    have h : z ∈ frontier (Icc (-2 : ℝ) 3 ×ℂ Icc (-2 : ℝ) 3) := hz
    simp only [Complex.frontier_reProdIm, frontier_Icc (by norm_num : (-2 : ℝ) ≤ 3),
      closure_Icc, mem_union, Complex.mem_reProdIm, mem_insert_iff,
      mem_singleton_iff] at h
    rcases h with ⟨-, h | h⟩ | ⟨h | h, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  rcases hz' with h | h | h | h
  · have hcoord : 1 ≤ |(z - w).im| := by
      have hneg := neg_le_abs (z - w).im
      simp only [Complex.sub_im] at hneg ⊢
      linarith [hw'.2.2.1]
    exact hcoord.trans (Complex.abs_im_le_norm (z - w)) |>.trans_eq
      (dist_eq_norm z w).symm
  · have hcoord : 1 ≤ |(z - w).im| := by
      have hpos := le_abs_self (z - w).im
      simp only [Complex.sub_im] at hpos ⊢
      linarith [hw'.2.2.2]
    exact hcoord.trans (Complex.abs_im_le_norm (z - w)) |>.trans_eq
      (dist_eq_norm z w).symm
  · have hcoord : 1 ≤ |(z - w).re| := by
      have hneg := neg_le_abs (z - w).re
      simp only [Complex.sub_re] at hneg ⊢
      linarith [hw'.1]
    exact hcoord.trans (Complex.abs_re_le_norm (z - w)) |>.trans_eq
      (dist_eq_norm z w).symm
  · have hcoord : 1 ≤ |(z - w).re| := by
      have hpos := le_abs_self (z - w).re
      simp only [Complex.sub_re] at hpos ⊢
      linarith [hw'.2.1]
    exact hcoord.trans (Complex.abs_re_le_norm (z - w)) |>.trans_eq
      (dist_eq_norm z w).symm

 
theorem laneC_unit_cross_coord_box (i : Bool) {z : ℂ}
    (hz : z ∈ laneCUnitUcross i) :
    z.re ∈ Icc (-3 : ℝ) 4 ∧ z.im ∈ Icc (-3 : ℝ) 4 := by
  cases i
  · change z ∈ laneCPrimeCross at hz
    have hclosed : IsClosed (Icc (-3 : ℝ) 4 ×ℂ Icc (-3 : ℝ) 4) :=
      isClosed_Icc.reProdIm isClosed_Icc
    have hsub : laneCUnitNeighborhood \ laneCUnitBlock ⊆
        Icc (-3 : ℝ) 4 ×ℂ Icc (-3 : ℝ) 4 := by
      intro x hx
      obtain ⟨w, hw, hdist⟩ :=
        Metric.mem_thickening_iff.mp hx.1
      have hw' : 0 ≤ w.re ∧ w.re ≤ 1 ∧ 0 ≤ w.im ∧ w.im ≤ 1 := by
        simpa [laneCUnitBlock, rectAB, MarkedRect.toSet,
          Complex.mem_reProdIm, mem_Icc, and_assoc] using hw
      have hre : |x.re - w.re| ≤ dist x w := by
        simpa [dist_eq_norm, Complex.sub_re] using Complex.abs_re_le_norm (x - w)
      have him : |x.im - w.im| ≤ dist x w := by
        simpa [dist_eq_norm, Complex.sub_im] using Complex.abs_im_le_norm (x - w)
      obtain ⟨hrelo, hrehi⟩ := abs_le.mp (hre.trans hdist.le)
      obtain ⟨himlo, himhi⟩ := abs_le.mp (him.trans hdist.le)
      simp only [Complex.mem_reProdIm, mem_Icc]
      constructor <;> constructor <;> linarith [hw'.1, hw'.2.1, hw'.2.2.1, hw'.2.2.2]
    have hbox : z ∈ Icc (-3 : ℝ) 4 ×ℂ Icc (-3 : ℝ) 4 :=
      closure_minimal hsub hclosed hz
    simpa only [Complex.mem_reProdIm] using hbox
  · change z ∈ laneCDoublePrimeCross at hz
    have hbox : z ∈ laneCOuterCluster := hz.1
    simp only [laneCOuterCluster, Complex.mem_reProdIm, mem_Icc] at hbox
    exact ⟨⟨by linarith [hbox.1.1], by linarith [hbox.1.2]⟩,
      by linarith [hbox.2.1], by linarith [hbox.2.2]⟩
end SupercriticalLQGUniqueness.B2.DG20Conc
