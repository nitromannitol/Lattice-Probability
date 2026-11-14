/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointUpperGeneral at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointMedianTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistDomainMono

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_non_dyadic_point_upper_general
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (hPos : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W)
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U) (hzw : z ≠ w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, ∀ s : ℝ, 0 < s → s ≤ 1 →
      let δ : ℝ := (2 : ℝ) ^ (-((n : ℝ) + s))
      P {ω | ENNReal.ofReal M <
        ENNReal.ofReal (lambdaDelta ξ W P δ)⁻¹ *
          lfppDOn (ξ : ℝ) (fun y => phiVer W P δ 1 y ω)
            U z w} ≤ ENNReal.ofReal ε := by
  obtain ⟨V, hV, hVc, hVb, hVU, hzV, hwV⟩ :=
    pt_dist_bounded_connected_core U hU hUc z w hz hw
  obtain ⟨M, hM, htail⟩ :=
    dg20_non_dyadic_point_median_tails hPerc hExp hPos
      ξ Q hQ P W hW V hV hVc hVb z w hzV hwV hzw ε hε
  refine ⟨M, hM, ?_⟩
  intro n s hs hs1
  dsimp only
  let δ : ℝ := (2 : ℝ) ^ (-((n : ℝ) + s))
  have hsub :
      {ω | ENNReal.ofReal M <
        ENNReal.ofReal (lambdaDelta ξ W P δ)⁻¹ *
          lfppDOn (ξ : ℝ) (fun y => phiVer W P δ 1 y ω)
            U z w} ⊆
      {ω | ENNReal.ofReal M <
        ENNReal.ofReal (lambdaDelta ξ W P δ)⁻¹ *
          lfppDOn (ξ : ℝ) (fun y => phiVer W P δ 1 y ω)
            V z w} := by
    intro ω hω
    change ENNReal.ofReal M <
      ENNReal.ofReal (lambdaDelta ξ W P δ)⁻¹ *
        lfppDOn (ξ : ℝ) (fun y => phiVer W P δ 1 y ω) U z w at hω
    change ENNReal.ofReal M <
      ENNReal.ofReal (lambdaDelta ξ W P δ)⁻¹ *
        lfppDOn (ξ : ℝ) (fun y => phiVer W P δ 1 y ω) V z w
    exact hω.trans_le (by
      gcongr
      exact pt_dist_mono_domain (ξ : ℝ)
        (fun y => phiVer W P δ 1 y ω) V U hVU z w)
  exact (measure_mono hsub).trans (htail n s hs hs1).1

end SupercriticalLQGUniqueness.B2.DG20Pt
