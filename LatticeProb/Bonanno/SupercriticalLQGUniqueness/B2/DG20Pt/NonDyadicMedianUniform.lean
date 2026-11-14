/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicMedianUniform at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicMedianLaw
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoise

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 
theorem dg20_non_dyadic_median_compare_uniform_of_perc
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) :
    ∃ C : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
      IsWhiteNoise P W → ∀ n : ℕ, ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        Real.exp (-C) * lambdaN ξ W P n ≤
          lambdaDelta ξ W P ((2 : ℝ) ^ (-((n : ℝ) + r))) ∧
        lambdaDelta ξ W P ((2 : ℝ) ^ (-((n : ℝ) + r))) ≤
          Real.exp C * lambdaN ξ W P n := by
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise
  let P₀ : Measure (ℕ → ℝ) := LQGDimension.ExistAsm.stdP
  obtain ⟨C, hC⟩ :=
    dg20_non_dyadic_median_compare_of_perc hPerc ξ P₀ W₀ hW₀
  refine ⟨C, ?_⟩
  intro Ω _ P _ W hW n r hr0 hr1
  let δ : ℝ := (2 : ℝ) ^ (-((n : ℝ) + r))
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hN := SupercriticalLQGUniqueness.Exponent.Median.lambdaN_eq_of_whiteNoise
    hW hW₀ (ξ : ℝ) n
  have hD := lambdaDelta_eq_of_whiteNoise hW hW₀ (ξ : ℝ) δ hδ0 hδ1
  change Real.exp (-C) * lambdaN ξ W P n ≤ lambdaDelta ξ W P δ ∧
    lambdaDelta ξ W P δ ≤ Real.exp C * lambdaN ξ W P n
  rw [hN, hD]
  exact hC n r hr0 hr1

end SupercriticalLQGUniqueness.B2.DG20Pt
