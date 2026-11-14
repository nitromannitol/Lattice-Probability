/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointLowerMedian at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointLowerLambda
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMedianLowerArithmetic
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicMedianUniform

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_non_dyadic_point_lower_median_small
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (z w : ℂ) (hzw : z ≠ w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 3 < T ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ U : Set ℂ, IsOpen U →
        ∀ n : ℕ, ∀ s : ℝ, 0 < s → s ≤ 1 →
          let δ : ℝ := (2 : ℝ) ^ (-((n : ℝ) + s))
          P {ω | lfppDOn (ξ : ℝ)
            (fun y => phiVer W P δ 1 y ω) U z w <
              ENNReal.ofReal
                (T⁻¹ * lambdaDelta ξ W P δ)} ≤
            ENNReal.ofReal ε := by
  obtain ⟨c, hc⟩ := dg20_non_dyadic_median_compare_uniform_of_perc hPerc ξ
  let A : ℝ := max 1 (Real.exp c)
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) hA1
  obtain ⟨T₀, hT₀, hlow⟩ :=
    dg20_non_dyadic_point_lower_lambda_small hPerc ξ z w hzw ε hε
  let T : ℝ := A * T₀
  have hT : 3 < T := by dsimp [T]; nlinarith
  refine ⟨T, hT, ?_⟩
  intro Ω _ P _ W hW U hU n s hs hs1
  dsimp only
  let δ : ℝ := (2 : ℝ) ^ (-((n : ℝ) + s))
  have hmed := hc P W hW n s hs.le hs1
  have hhigh : lambdaDelta ξ W P δ ≤ A * lambdaN ξ W P n := by
    calc
      lambdaDelta ξ W P δ ≤
          Real.exp c * lambdaN ξ W P n := hmed.2
      _ ≤ A * lambdaN ξ W P n := by
        exact mul_le_mul_of_nonneg_right
          (le_max_right 1 (Real.exp c)) (lambdaN_pos hW n).le
  have hsub :
      {ω | lfppDOn (ξ : ℝ)
        (fun y => phiVer W P δ 1 y ω) U z w <
          ENNReal.ofReal (T⁻¹ * lambdaDelta ξ W P δ)} ⊆
      {ω | lfppDOn (ξ : ℝ)
        (fun y => phiVer W P δ 1 y ω) U z w <
          ENNReal.ofReal (T₀⁻¹ * lambdaN ξ W P n)} := by
    intro ω hω
    change lfppDOn (ξ : ℝ)
      (fun y => phiVer W P δ 1 y ω) U z w <
        ENNReal.ofReal (T⁻¹ * lambdaDelta ξ W P δ) at hω
    exact pt_dist_median_lower_event
      (lambdaN ξ W P n) (lambdaDelta ξ W P δ) A T₀
      hA (by linarith) hhigh _ hω
  exact (measure_mono hsub).trans (hlow P W hW U hU n s hs hs1)

end SupercriticalLQGUniqueness.B2.DG20Pt
