/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCShortPiece at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCShortHit

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

private def laneCShortInnerSource : Bool → Set ℂ
  | false => laneCUnitBlock
  | true => laneCInnerCluster

private theorem laneC_short_inner_infDist_zero (i : Bool) {z : ℂ}
    (hz : z ∈ laneCUnitInner i) :
    Metric.infDist z (laneCShortInnerSource i) = 0 := by
  cases i
  · exact laneC_prime_inner_infDist_zero hz
  · exact laneC_double_prime_inner_infDist_zero hz

private theorem laneC_short_outer_infDist_ge_one (i : Bool) {z : ℂ}
    (hz : z ∈ laneCUnitOuter i) :
    1 ≤ Metric.infDist z (laneCShortInnerSource i) := by
  cases i
  · exact (laneC_prime_outer_infDist_one hz).ge
  · exact laneC_double_prime_outer_infDist_ge_one hz

private theorem laneC_open_hatBox_subset_hatBox (b : ℤ × ℤ) :
    (Ioo (((b.1 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ 3)
          (((b.1 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ 3) ×ℂ
      Ioo (((b.2 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ 3)
          (((b.2 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ 3)) ⊆ T20D.hatBox 3 b := by
  intro x hx
  simp only [T20D.hatBox, Complex.mem_reProdIm, mem_Ioo, mem_Icc] at hx ⊢
  exact ⟨⟨hx.1.1.le, hx.1.2.le⟩, hx.2.1.le, hx.2.2.le⟩

 

theorem laneC_short_piece_of_small_annulus
    (i : Bool) {ξ : ℝ} {f : ℂ → ℝ} {G : ℝ → ℂ} {z w : ℂ}
    (hG : IsPiecewiseC1Path G z w)
    (hz : z ∈ laneCUnitInner i) (hw : w ∈ laneCUnitOuter i)
    (hmap : MapsTo G (Icc (0 : ℝ) 1) (laneCUnitUcross i)) :
    ∃ b ∈ laneCShortBlocks, ∃ j ∈ T20D.shortJ 3 b,
      crossLenIn ξ f (T20D.RS 3 j) (T20D.RS₁ 3 j) (T20D.RS₂ 3 j) ≤
        lfppLen ξ f G := by
  have hstart : Metric.infDist (G 0) (laneCShortInnerSource i) = 0 := by
    rw [hG.source]
    exact laneC_short_inner_infDist_zero i hz
  have hend : 1 ≤ Metric.infDist (G 1) (laneCShortInnerSource i) := by
    rw [hG.target]
    exact laneC_short_outer_infDist_ge_one i hw
  obtain ⟨t, ht, hhalf⟩ :=
    laneC_crossing_hits_half_dist (laneCShortInnerSource i)
      hG.continuousOn hstart hend
  have hcoord := laneC_unit_cross_coord_box i (hmap ht)
  obtain ⟨b, hb, hvisit⟩ := laneC_short_grid_covers hcoord.1 hcoord.2
  have hout : G 1 ∉
      Ioo (((b.1 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ 3)
          (((b.1 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ 3) ×ℂ
      Ioo (((b.2 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ 3)
          (((b.2 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ 3) := by
    intro hbox
    have hhat := laneC_open_hatBox_subset_hatBox b hbox
    have hdist := laneC_short_hatBox_dist_lt_half hvisit hhat
    have htri : Metric.infDist (G 1) (laneCShortInnerSource i) ≤
        Metric.infDist (G t) (laneCShortInnerSource i) + dist (G 1) (G t) :=
      Metric.infDist_le_infDist_add_dist
    linarith [dist_comm (G 1) (G t)]
  obtain ⟨u, v, htu, huv, hv1, _, j, hj, hadm⟩ :=
    T20D.piece_of_cross hG ht hvisit hout
  have hu0 : 0 ≤ u := ht.1.trans htu
  have hsub : lfppLen ξ f (subPath G u v) ≤ lfppLen ξ f G := by
    rw [lfppLen_subPath G huv, lfppLen_eq]
    exact lintegral_mono_set (Icc_subset_Icc hu0 hv1)
  exact ⟨b, hb, j, hj, (crossLenIn_le_lfppLen (ξ := ξ) (f := f) hadm).trans hsub⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
