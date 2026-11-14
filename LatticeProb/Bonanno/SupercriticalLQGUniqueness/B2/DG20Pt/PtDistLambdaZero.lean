/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLambdaZero at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Zero

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_lambdaN_zero_ge_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ξ : ℝ) : 1 ≤ lambdaN ξ W P 0 := by
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let Y : ℂ → Ω → ℝ := phiMN W P 0 0
  let R : MarkedRect := rectAB 1 1
  have hY := isPhiVersion_phiMN hW (le_refl 0)
  have hnull : P {ω | ¬ ∀ x ∈ R.toSet, |Y x ω| ≤ 0} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_phiMN_zero_zero hW] with ω hω hbad
    apply hbad
    intro x hx
    simp only [Y, hω x, abs_zero, le_refl]
  have hsmall : P {ω | ¬ ∀ x ∈ R.toSet, |Y x ω| ≤ 0} < 2⁻¹ := by
    rw [hnull]
    norm_num
  have h := le_lowerMedian_lenObs (ξ := ξ) (P := P) hY.cont hY.meas
    R (by norm_num [R, rectAB]) (by norm_num [R, rectAB]) hsmall
  simpa [Y, R, lambdaN, lenN, lenMN, rectAB, MarkedRect.crossWidth] using h

end SupercriticalLQGUniqueness.B2.DG20Pt
