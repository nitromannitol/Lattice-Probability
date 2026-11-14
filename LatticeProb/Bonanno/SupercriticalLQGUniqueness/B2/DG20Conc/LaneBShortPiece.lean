/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBShortPiece at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBBoundaryFamily

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

private theorem laneB_open_box_subset_hatBox (b : ℤ × ℤ) :
    (Ioo ((b.1 : ℝ) - 1) ((b.1 : ℝ) + 2) ×ℂ
      Ioo ((b.2 : ℝ) - 1) ((b.2 : ℝ) + 2)) ⊆ T20D.hatBox 0 b := by
  intro x hx
  simp only [T20D.hatBox, pow_zero, mul_one, Complex.mem_reProdIm,
    mem_Ioo, mem_Icc] at hx ⊢
  exact ⟨⟨hx.1.1.le, hx.1.2.le⟩, hx.2.1.le, hx.2.2.le⟩

 


theorem laneB_short_piece_of_radial_path
    {R : ℝ} (hR : 24 ≤ R) {G : ℝ → ℂ} {z w : ℂ}
    (hG : IsPiecewiseC1Path G z w)
    (hz : ‖z‖ = R) (hw : ‖w‖ = 2 * R) :
    ∃ b ∈ laneBBoundaryBlocks (laneBGridRadius R),
      ∃ u v : ℝ, 0 ≤ u ∧ u < v ∧ v ≤ 1 ∧
        (∀ r ∈ Icc u v, revPath G r ∈ T20D.hatBox 0 b) ∧
        ∃ j ∈ T20D.shortJ 0 b,
          AdmPath (T20D.RS 0 j) (T20D.RS₁ 0 j) (T20D.RS₂ 0 j)
            (subPath (revPath G) u v) := by
  have hstart : ‖G 0‖ = R := by rw [hG.source]; exact hz
  have hend : ‖G 1‖ = 2 * R := by rw [hG.target]; exact hw
  obtain ⟨t, ht, b, hb, hvisit⟩ :=
    laneB_annulus_crossing_visits_boundaryFamily hR hG.continuousOn hstart hend
  have hrev : IsPiecewiseC1Path (revPath G) w z :=
    isPiecewiseC1Path_revPath hG
  have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hvisit' : revPath G (1 - t) ∈ T20.dyBlock 0 b := by
    simpa [revPath] using hvisit
  have hout : revPath G 1 ∉
      Ioo (((b.1 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ 0) (((b.1 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ 0) ×ℂ
      Ioo (((b.2 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ 0) (((b.2 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ 0) := by
    simp only [pow_zero, mul_one]
    intro hmem
    have hbox := laneB_open_box_subset_hatBox b hmem
    have hne := laneB_inner_sphere_outside_boundary_hatBox hR hb hz
    apply hne
    simpa [revPath, hG.source] using hbox
  obtain ⟨u, v, hu, huv, hv, hbox, j, hj, hadm⟩ :=
    T20D.piece_of_cross hrev ht' hvisit' hout
  exact ⟨b, hb, u, v, ht'.1.trans hu, huv, hv, hbox, j, hj, hadm⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
