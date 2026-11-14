/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.SquareCrossTailThreshold at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.SquareCrossQuantileWindow
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateLinear
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BTight

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem square_cross_two_tails_small
    (cU aU cL aL p : ℝ)
    (hcU : 0 < cU) (haU : 0 < aU)
    (hcL : 0 < cL) (haL : 0 < aL) (hp : 0 < p) :
    ∃ T : ℝ, 3 < T ∧
      cU * Real.exp (-aU * (Real.log T) ^ 2 /
        Real.log (Real.log T)) < p ∧
      cL * Real.exp (-aL * (Real.log T) ^ 2) < p := by
  obtain ⟨H, hH, hlarge⟩ :=
    pt_dist_rate_linear_large aU 1 haU one_pos
  let s : ℝ := max H (max (Real.log (2 * cU / p))
    (Real.log (2 * cL / p) / aL))
  have hsH : H ≤ s := le_max_left _ _
  have hsU : Real.log (2 * cU / p) ≤ s :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hsL : Real.log (2 * cL / p) / aL ≤ s :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hs3 : 3 ≤ s := hH.trans hsH
  let T : ℝ := Real.exp s
  have hT : 3 < T := by
    have he := Real.add_one_le_exp s
    dsimp [T]
    linarith
  refine ⟨T, hT, ?_, ?_⟩
  · have hrate : s ≤ aU * (s ^ 2 / Real.log s) := by
      simpa only [one_mul] using hlarge s hsH
    have hhalf : cU * Real.exp (-s) ≤ p / 2 := by
      simpa only [one_mul] using
        (LQGMetric.DDDF.T20B.mul_exp_neg_le_half hcU one_pos hp
          (by simpa only [div_one] using hsU))
    have hcomp : cU * Real.exp
        (-aU * (Real.log T) ^ 2 / Real.log (Real.log T)) ≤
        cU * Real.exp (-s) := by
      dsimp [T]
      simp only [Real.log_exp]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hcU.le
      calc
        -aU * s ^ 2 / Real.log s = -(aU * (s ^ 2 / Real.log s)) := by ring
        _ ≤ -s := neg_le_neg hrate
    linarith
  · have hhalf : cL * Real.exp (-(aL * s)) ≤ p / 2 :=
      LQGMetric.DDDF.T20B.mul_exp_neg_le_half hcL haL hp hsL
    have hs2 : s ≤ s ^ 2 := by nlinarith
    have hcomp : cL * Real.exp (-aL * (Real.log T) ^ 2) ≤
        cL * Real.exp (-(aL * s)) := by
      dsimp [T]
      simp only [Real.log_exp]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hcL.le
      nlinarith [mul_le_mul_of_nonneg_left hs2 haL.le]
    linarith

end SupercriticalLQGUniqueness.B2.DG20Pt
