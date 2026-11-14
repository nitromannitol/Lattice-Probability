/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.RealSquareCrossSmall at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.RealSquareCrossUniform
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateLinear
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BTight

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_real_square_cross_tails_small_uniform
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (η : ℝ) (hη : 0 < η) :
    ∃ s : ℝ, 2 < s ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ δ : Ioo (0 : ℝ) 1,
          P {ω | Real.exp s * lambdaDelta ξ W P δ ≤
            lenObs ξ (phiVer W P δ 1) (rectAB 1 1) ω} ≤
            ENNReal.ofReal η ∧
          P {ω | lenObs ξ (phiVer W P δ 1) (rectAB 1 1) ω ≤
            Real.exp (-s) * lambdaDelta ξ W P δ} ≤
            ENNReal.ofReal η := by
  obtain ⟨cU, CU, cL, CL, hcU, hCU, hcL, hCL, htail⟩ :=
    dg20_real_square_cross_tails_uniform_of_perc hPerc ξ
  obtain ⟨H, hH, hlarge⟩ := pt_dist_rate_linear_large cU 1 hcU one_pos
  let s : ℝ := max H (max (Real.log (2 * CU / η))
    (Real.log (2 * CL / η) / cL))
  have hsH : H ≤ s := le_max_left _ _
  have hsU : Real.log (2 * CU / η) ≤ s :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hsL : Real.log (2 * CL / η) / cL ≤ s :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hs3 : 3 ≤ s := hH.trans hsH
  have hrate : s ≤ cU * (s ^ 2 / Real.log s) := by
    simpa only [one_mul] using hlarge s hsH
  have hupper : CU * Real.exp (-cU * s ^ 2 / Real.log s) ≤ η := by
    have hhalf : CU * Real.exp (-s) ≤ η / 2 := by
      simpa only [one_mul] using
        (T20B.mul_exp_neg_le_half hCU one_pos hη
          (by simpa only [div_one] using hsU))
    have hcomp : CU * Real.exp (-cU * s ^ 2 / Real.log s) ≤
        CU * Real.exp (-s) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCU.le
      calc
        -cU * s ^ 2 / Real.log s = -(cU * (s ^ 2 / Real.log s)) := by ring
        _ ≤ -s := neg_le_neg hrate
    linarith
  have hlower : CL * Real.exp (-cL * s ^ 2) ≤ η := by
    have hhalf : CL * Real.exp (-(cL * s)) ≤ η / 2 :=
      T20B.mul_exp_neg_le_half hCL hcL hη hsL
    have hs2 : s ≤ s ^ 2 := by nlinarith
    have hcomp : CL * Real.exp (-cL * s ^ 2) ≤
        CL * Real.exp (-(cL * s)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCL.le
      nlinarith [mul_le_mul_of_nonneg_left hs2 hcL.le]
    linarith
  refine ⟨s, by linarith, ?_⟩
  intro Ω _ P _ W hW δ
  obtain ⟨hu, hl⟩ := htail P W hW s (by linarith) δ
  exact ⟨hu.trans (ENNReal.ofReal_le_ofReal hupper),
    hl.trans (ENNReal.ofReal_le_ofReal hlower)⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
