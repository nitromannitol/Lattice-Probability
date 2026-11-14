/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.SquareCrossQuantileRatio at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.SquareCrossTailThreshold

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem dg20_all_small_quantile_ratio_of_perc
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (p : ℝ) (hp : 0 < p) (hp2 : p < 1 / 2) :
    ∃ B : ℝ, 0 < B ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ,
          LambdaN ξ W P n (ENNReal.ofReal p) ≤ B := by
  obtain ⟨cU, aU, hcU, haU, hU⟩ := square_cross_upper_tail_of_inputs hPerc ξ
  obtain ⟨cL, aL, hcL, haL, hL⟩ := square_cross_lower_tail_of_inputs hPerc ξ
  obtain ⟨T, hT, hUT, hLT⟩ :=
    square_cross_two_tails_small cU aU cL aL p hcU haU hcL haL hp
  have hT0 : 0 < T := by linarith
  refine ⟨T ^ 2, by positivity, ?_⟩
  intro Ω _ P _ W hW n
  have hpq0 : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.2 hp
  have hpq1 : ENNReal.ofReal p < 1 := ENNReal.ofReal_lt_one.mpr (by linarith)
  unfold LambdaN
  refine Finset.sup'_le _ _ fun k hk => ?_
  have hlo : P {ω | lenObs ξ (phiMN W P 0 k) (rectAB 1 1) ω <
      T⁻¹ * lambdaN ξ W P k} < ENNReal.ofReal p :=
    (hL P W hW k T hT).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hp).2 hLT)
  have hhi : P {ω | T * lambdaN ξ W P k <
      lenObs ξ (phiMN W P 0 k) (rectAB 1 1) ω} < ENNReal.ofReal p :=
    (hU P W hW k T hT).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hp).2 hUT)
  have hwindow := square_cross_quantile_window_of_tails P W hW
    (ξ : ℝ) k p T hp (by linarith) hT0 hlo hhi
  have hℓ : 0 < ellN ξ W P k (ENNReal.ofReal p) :=
    T20B.ellN_pos hW hpq0 hpq1 k
  have hLam : lambdaN ξ W P k ≤
      T * ellN ξ W P k (ENNReal.ofReal p) := by
    calc
      lambdaN ξ W P k = T * (T⁻¹ * lambdaN ξ W P k) := by
        field_simp
      _ ≤ T * ellN ξ W P k (ENNReal.ofReal p) :=
        mul_le_mul_of_nonneg_left hwindow.1 hT0.le
  apply (div_le_iff₀ hℓ).2
  calc
    ellBarN ξ W P k (ENNReal.ofReal p) ≤ T * lambdaN ξ W P k := hwindow.2
    _ ≤ T * (T * ellN ξ W P k (ENNReal.ofReal p)) :=
      mul_le_mul_of_nonneg_left hLam hT0.le
    _ = T ^ 2 * ellN ξ W P k (ENNReal.ofReal p) := by ring

end SupercriticalLQGUniqueness.B2.DG20Pt
