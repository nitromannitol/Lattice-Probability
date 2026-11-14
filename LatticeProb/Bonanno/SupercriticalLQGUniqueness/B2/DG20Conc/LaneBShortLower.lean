/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBShortLower at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBShortPiece
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Geom

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

 

theorem laneB_short_crossLen_le_radial_pathLen
    {R : ℝ} (hR : 24 ≤ R) (ξ : ℝ) (f : ℂ → ℝ)
    {G : ℝ → ℂ} {z w : ℂ}
    (hG : IsPiecewiseC1Path G z w)
    (hz : ‖z‖ = R) (hw : ‖w‖ = 2 * R) :
    ∃ b ∈ laneBBoundaryBlocks (laneBGridRadius R),
      ∃ j ∈ T20D.shortJ 0 b,
        crossLenIn ξ f (T20D.RS 0 j) (T20D.RS₁ 0 j) (T20D.RS₂ 0 j) ≤
          lfppLen ξ f G := by
  obtain ⟨b, hb, u, v, hu, huv, hv, _, j, hj, hadm⟩ :=
    laneB_short_piece_of_radial_path hR hG hz hw
  have hcross := crossLenIn_le_lfppLen (ξ := ξ) (f := f) hadm
  have hsub : lfppLen ξ f (subPath (revPath G) u v) ≤ lfppLen ξ f (revPath G) := by
    rw [lfppLen_subPath (revPath G) huv, lfppLen_eq]
    exact lintegral_mono_set (Icc_subset_Icc hu hv)
  refine ⟨b, hb, j, hj, ?_⟩
  exact hcross.trans (hsub.trans_eq (lfppLen_revPath G))

 


theorem laneB_short_family_le_annulus_crossLen
    {R : ℝ} (hR : 24 ≤ R) (ξ : ℝ) (f : ℂ → ℝ) :
    (⨅ b ∈ laneBBoundaryBlocks (laneBGridRadius R),
       ⨅ j ∈ T20D.shortJ 0 b,
         crossLenIn ξ f (T20D.RS 0 j) (T20D.RS₁ 0 j) (T20D.RS₂ 0 j)) ≤
      crossLenIn ξ f
        {z : ℂ | dist z 0 ∈ Icc R (2 * R)}
        (sphere (0 : ℂ) R) (sphere (0 : ℂ) (2 * R)) := by
  apply le_crossLenIn
  intro G hG
  obtain ⟨z, hz, w, hw, hpath, -⟩ := hG
  have hz' : ‖z‖ = R := by simpa [mem_sphere, dist_zero_right] using hz
  have hw' : ‖w‖ = 2 * R := by simpa [mem_sphere, dist_zero_right] using hw
  obtain ⟨b, hb, j, hj, hle⟩ :=
    laneB_short_crossLen_le_radial_pathLen hR ξ f hpath hz' hw'
  exact (iInf₂_le b hb).trans ((iInf₂_le j hj).trans hle)

theorem laneB_short_rectangle_of_annulus_small
    {R : ℝ} (hR : 24 ≤ R) (ξ : ℝ) (f : ℂ → ℝ) (a : ℝ)
    (hsmall : crossLenIn ξ f
      {z : ℂ | dist z 0 ∈ Icc R (2 * R)}
      (sphere (0 : ℂ) R) (sphere (0 : ℂ) (2 * R)) < ENNReal.ofReal a) :
    ∃ b ∈ laneBBoundaryBlocks (laneBGridRadius R),
      ∃ j ∈ T20D.shortJ 0 b,
        T20B.mrectLen ξ f 0 j.1 j.2 1 3 < a := by
  have h := (laneB_short_family_le_annulus_crossLen hR ξ f).trans_lt hsmall
  obtain ⟨b, hb'⟩ := iInf_lt_iff.mp h
  obtain ⟨hb, hj'⟩ := iInf_lt_iff.mp hb'
  obtain ⟨j, hj''⟩ := iInf_lt_iff.mp hj'
  obtain ⟨hj, hlt⟩ := iInf_lt_iff.mp hj''
  refine ⟨b, hb, j, hj, ?_⟩
  exact ENNReal.toReal_lt_of_lt_ofReal hlt

end SupercriticalLQGUniqueness.B2.DG20Conc
