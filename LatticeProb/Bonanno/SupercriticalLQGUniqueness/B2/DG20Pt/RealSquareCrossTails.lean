/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.RealSquareCrossTails at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicMedianCompare
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6TailsAB5

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_real_square_cross_tails_of_perc
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ s : ℝ, 2 < s → ∀ δ : ℝ, 0 < δ → δ < 1 →
        P {ω | Real.exp s * lambdaDelta ξ W P δ ≤
          lenObs ξ (phiVer W P δ 1) (rectAB 1 1) ω} ≤
          ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s))) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ s : ℝ, 2 < s → ∀ δ : ℝ, 0 < δ → δ < 1 →
        P {ω | lenObs ξ (phiVer W P δ 1) (rectAB 1 1) ω ≤
          Real.exp (-s) * lambdaDelta ξ W P δ} ≤
          ENNReal.ofReal (C * Real.exp (-c * s ^ 2))) := by
  haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hLambda : ∃ p₀ : ℝ, 0 < p₀ ∧
      ∀ p : ℝ, 0 < p → p ≤ p₀ →
        ∃ B : ℝ, ∀ n,
          LambdaN ξ W P n (ENNReal.ofReal p) ≤ B := by
    refine ⟨1 / 4, by norm_num, ?_⟩
    intro p hp hpp
    obtain ⟨B, _, hratio⟩ :=
      dg20_all_small_quantile_ratio_of_perc hPerc ξ p hp (by linarith)
    exact ⟨B, hratio (Ω := Ω) P W hW⟩
  exact ⟨S6AB.s6_eq6_102_AB hW ξ.property hLambda
      (by norm_num) (by norm_num),
    S6AB.s6_eq6_103_AB hW ξ.property hLambda
      (by norm_num) (by norm_num)⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
