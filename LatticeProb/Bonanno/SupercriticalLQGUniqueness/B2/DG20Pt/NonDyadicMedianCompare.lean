/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicMedianCompare at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.SquareCrossQuantileRatio
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Eq698Main

 


set_option autoImplicit false
noncomputable section

open MeasureTheory
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem dg20_non_dyadic_median_compare_of_perc
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Set.Ioi (0 : ℝ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) :
    S6Eq6_98 ξ W P := by
  have hLambda : ∃ p₀ : ℝ, 0 < p₀ ∧
      ∀ p : ℝ, 0 < p → p ≤ p₀ →
        ∃ B : ℝ, ∀ n,
          LambdaN ξ W P n (ENNReal.ofReal p) ≤ B := by
    refine ⟨1 / 4, by norm_num, ?_⟩
    intro p hp hpp
    haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
    obtain ⟨B, hB, hratio⟩ :=
      dg20_all_small_quantile_ratio_of_perc hPerc ξ p hp (by linarith)
    refine ⟨B, ?_⟩
    exact hratio (Ω := Ω) P W hW
  exact s6_eq6_98_of_Lambda hW ξ.property hLambda

end SupercriticalLQGUniqueness.B2.DG20Pt
