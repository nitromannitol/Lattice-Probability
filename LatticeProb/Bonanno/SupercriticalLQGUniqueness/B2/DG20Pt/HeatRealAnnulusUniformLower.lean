/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatRealAnnulusUniformLower at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatRealAnnulusLowerMedian
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28U1Aux

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_white_noise_annulus_lower_uniform_of_perc
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (z : ℂ) (d : ℝ) (hd : 0 < d)
    (η : ℝ) (hη : 0 < η) :
    ∃ T : ℝ, 3 < T ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ δ : Ioo (0 : ℝ) 1,
        P {ω | crossLenIn (ξ : ℝ)
          (fun y => phiVer W P δ 1 y ω)
          (closedBall z d) (sphere z (d / 16))
          (sphere z (3 * d / 4)) <
            ENNReal.ofReal (T⁻¹ * lambdaDelta ξ W P δ)} ≤
          ENNReal.ofReal η := by
  obtain ⟨T, hT, htail⟩ :=
    dg20_real_annulus_lower_median_small hPerc ξ z d hd η hη
  refine ⟨T, hT, ?_⟩
  intro Ω _ P _ W hW δ
  obtain ⟨n, s, hs, hs1, hδ⟩ :=
    S6P28U.exists_split' δ.property.1 δ.property.2
  change (δ : ℝ) = _ at hδ
  simpa only [hδ] using htail P W hW n s hs hs1

end SupercriticalLQGUniqueness.B2.DG20Pt
