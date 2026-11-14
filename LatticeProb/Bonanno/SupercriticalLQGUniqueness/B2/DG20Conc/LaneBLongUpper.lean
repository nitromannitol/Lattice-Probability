/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBLongUpper at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBAroundUpper

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

 


theorem laneB_long_rectangle_of_large_around {R : ℝ} (hR : 24 ≤ R)
    (ξ : ℝ) (f : ℂ → ℝ) (hf : Continuous f) (bnd : ℝ)
    (hlarge : ENNReal.ofReal (400 * R * bnd) <
      (lfppContMetric ξ f hf).aroundDist
        {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R}
        (sphere 0 R) (sphere 0 (2 * R))) :
    ∃ j ∈ laneBLongRects R,
      bnd < T20B.mrectLen ξ f 0 j.1 j.2 3 1 := by
  classical
  by_contra! hnot
  let m := laneBGridRadius R
  let N := (4 * (2 * m + 1)).toNat
  let M : ℕ := 36 * (N + 1)
  have hm : 0 ≤ m := by
    have h := (laneB_grid_radius_bounds hR).1
    have : (0 : ℝ) ≤ (m : ℝ) := by dsimp [m]; linarith
    exact_mod_cast this
  have hq : 0 ≤ 4 * (2 * m + 1) := by omega
  have hb0 : laneBPerimeterBlock m 0 ∈ laneBBoundaryBlocks m :=
    laneB_perimeterBlock_mem hm (by omega)
  let j₀ := S6U.siteJ 0 (laneBPerimeterBlock m 0) 0
  have hj₀ : j₀ ∈ laneBLongRects R := by
    exact laneB_siteJ_mem_longRects (by simpa only [m] using hb0) 0
  have hbnd : 0 ≤ bnd := by
    have h0 := hnot j₀ hj₀
    have hn : 0 ≤ T20B.mrectLen ξ f 0 j₀.1 j₀.2 3 1 := by
      unfold T20B.mrectLen
      exact ENNReal.toReal_nonneg
    linarith
  have hcount : ((N + 1 : ℕ) : ℝ) ≤ 11 * R := by
    have h := laneB_perimeter_order_length_le hR
    have hN : (N : ℤ) = 4 * (2 * m + 1) := Int.toNat_of_nonneg hq
    have hNreal : ((N : ℕ) : ℝ) = (4 * (2 * m + 1) : ℤ) := by
      exact_mod_cast hN
    push_cast at h hNreal ⊢
    linarith
  have hfactor : (M : ℝ) ≤ 400 * R := by
    dsimp [M]
    push_cast at hcount ⊢
    nlinarith [hcount, hR]
  have hbound := laneB_large_aroundDist_le_cost hf hR hnot
  have hM :
      (lfppContMetric ξ f hf).aroundDist
          {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R}
          (sphere 0 R) (sphere 0 (2 * R)) ≤
        (M : ℝ≥0∞) * ENNReal.ofReal bnd := by
    convert hbound using 1 <;> dsimp [M, N, m] <;> push_cast <;> ring
  have hreal : (M : ℝ) * bnd ≤ (400 * R) * bnd :=
    mul_le_mul_of_nonneg_right hfactor hbnd
  have hcmp : (M : ℝ≥0∞) * ENNReal.ofReal bnd ≤
      ENNReal.ofReal (400 * R * bnd) := by
    calc
      (M : ℝ≥0∞) * ENNReal.ofReal bnd =
          ENNReal.ofReal ((M : ℝ) * bnd) := by
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg M)]
            simp
      _ ≤ ENNReal.ofReal (400 * R * bnd) :=
        ENNReal.ofReal_le_ofReal hreal
  exact (hM.trans hcmp).not_gt hlarge

end SupercriticalLQGUniqueness.B2.DG20Conc
