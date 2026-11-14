/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointTight at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointGeneralTails
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28U1Aux

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_white_noise_point_two_sided_tight_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (hPos : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W)
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U) (hzw : z ≠ w) :
    SupercriticalLQGUniqueness.IsTwoSidedTight P
      (fun δ : Ioo (0 : ℝ) 1 => fun ω =>
        ENNReal.ofReal (lambdaDelta ξ W P δ)⁻¹ *
          lfppDOn (ξ : ℝ) (fun y => phiVer W P δ 1 y ω) U z w) := by
  constructor
  · intro δ
    have hφ := isPhiVersion_phiVer hW δ.property.1 δ.property.2.le
    have hDm := pt_dist_measurable_lfppDOn_open (ξ : ℝ)
      U hU z w hφ.cont hφ.meas
    exact (measurable_const.mul hDm).aemeasurable
  · intro ε hε
    obtain ⟨M, hM, htail⟩ :=
      dg20_non_dyadic_point_general_tails hPerc hExp hPos ξ Q hQ
        P W hW U hU hUc z w hz hw hzw ε hε
    refine ⟨M, hM, ?_⟩
    intro δ
    obtain ⟨n, s, hs, hs1, hδ⟩ :=
      S6P28U.exists_split' δ.property.1 δ.property.2
    change (δ : ℝ) = _ at hδ
    simpa only [hδ] using htail n s hs hs1

end SupercriticalLQGUniqueness.B2.DG20Pt
