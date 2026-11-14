/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatRealAnnulusLowerMedian at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatRealAnnulusLowerLambda
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicMedianUniform
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMedianLowerArithmetic

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_real_annulus_lower_median_small
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (z : ℂ) (d : ℝ) (hd : 0 < d)
    (η : ℝ) (hη : 0 < η) :
    ∃ T : ℝ, 3 < T ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ, ∀ s : ℝ, 0 < s → s ≤ 1 →
        let δ : ℝ := (2 : ℝ) ^ (-((n : ℝ) + s))
        P {ω | crossLenIn (ξ : ℝ)
          (fun y => phiVer W P δ 1 y ω)
          (closedBall z d) (sphere z (d / 16))
          (sphere z (3 * d / 4)) <
            ENNReal.ofReal (T⁻¹ * lambdaDelta ξ W P δ)} ≤
          ENNReal.ofReal η := by
  obtain ⟨c, hc⟩ := dg20_non_dyadic_median_compare_uniform_of_perc hPerc ξ
  let A : ℝ := max 1 (Real.exp c)
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) hA1
  obtain ⟨T₀, hT₀, hlow⟩ :=
    dg20_real_annulus_lower_lambda_small hPerc ξ z d hd η hη
  let T : ℝ := A * T₀
  have hT : 3 < T := by dsimp [T]; nlinarith
  refine ⟨T, hT, ?_⟩
  intro Ω _ P _ W hW n s hs hs1
  dsimp only
  let δ : ℝ := (2 : ℝ) ^ (-((n : ℝ) + s))
  have hmed := hc P W hW n s hs.le hs1
  have hhigh : lambdaDelta ξ W P δ ≤ A * lambdaN ξ W P n := by
    calc
      lambdaDelta ξ W P δ ≤ Real.exp c * lambdaN ξ W P n := hmed.2
      _ ≤ A * lambdaN ξ W P n :=
        mul_le_mul_of_nonneg_right (le_max_right 1 (Real.exp c))
          (lambdaN_pos hW n).le
  let D : Ω → ℝ≥0∞ := fun ω => crossLenIn (ξ : ℝ)
    (fun y => phiVer W P δ 1 y ω)
    (closedBall z d) (sphere z (d / 16)) (sphere z (3 * d / 4))
  have hsub : {ω | D ω < ENNReal.ofReal (T⁻¹ * lambdaDelta ξ W P δ)} ⊆
      {ω | D ω < ENNReal.ofReal (T₀⁻¹ * lambdaN ξ W P n)} := by
    intro ω hω
    exact pt_dist_median_lower_event
      (lambdaN ξ W P n) (lambdaDelta ξ W P δ) A T₀
      hA (by linarith) hhigh _ hω
  change P {ω | D ω < ENNReal.ofReal (T⁻¹ * lambdaDelta ξ W P δ)} ≤
    ENNReal.ofReal η
  exact (measure_mono hsub).trans (hlow P W hW n s hs hs1)

end SupercriticalLQGUniqueness.B2.DG20Pt
