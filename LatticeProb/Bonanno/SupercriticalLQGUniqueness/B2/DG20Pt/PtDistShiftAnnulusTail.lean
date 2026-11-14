/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistShiftAnnulusTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistCompactAnnulusTail

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_shift_annulus_lower_tail_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (d : ℝ) (hd : 0 < d) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ, ∀ c : ℂ, ∀ T : ℝ, 3 < T →
          P {ω | crossLenIn (ξ : ℝ)
            (fun x => phiMN W P 0 n x ω)
            (closedBall c (3 * d / 4))
            (sphere c (d / 4)) (sphere c (d / 2)) <
              ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} ≤
            ENNReal.ofReal (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2)) := by
  obtain ⟨c₀, c₁, hc₀, hc₁, htail⟩ :=
    pt_dist_compact_annulus_lower_tail_of_inputs hPerc ξ d hd
  refine ⟨c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW n c T hT
  have hlaw := pt_dist_compact_annulus_law_shift
    P W hW (ξ : ℝ) n c (3 * d / 4) (d / 4) (d / 2)
    (measurableSet_Iio : MeasurableSet
      (Iio (ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n))))
  have hlaw' :
      P {ω | crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
        (closedBall c (3 * d / 4))
        (sphere c (d / 4)) (sphere c (d / 2)) <
          ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} =
      P {ω | crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
        (closedBall 0 (3 * d / 4))
        (sphere 0 (d / 4)) (sphere 0 (d / 2)) <
          ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} := by
    simpa only [mem_Iio, mem_ofPred_eq] using hlaw
  exact hlaw'.le.trans (htail P W hW n T hT)

end SupercriticalLQGUniqueness.B2.DG20Pt
