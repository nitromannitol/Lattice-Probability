/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingLowerSmall at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingLowerTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistDyadicLowerTail

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_moving_lower_tail_small_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (U : Set ℂ) (z w : ℂ) (hzw : z ≠ w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 3 < T ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ, ∀ r : ℝ, 1 ≤ r →
          P {ω | lfppDOn (ξ : ℝ)
            (fun y => phiMN W P 0 n y ω)
            ((fun x : ℂ => (r : ℂ) * x) '' U)
            ((r : ℂ) * z) ((r : ℂ) * w) <
              ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} ≤
            ENNReal.ofReal ε := by
  obtain ⟨c₀, c₁, hc₀, hc₁, htail⟩ :=
    pt_dist_moving_lower_tail_of_inputs hPerc ξ z w hzw
  obtain ⟨T, hT, hsmall⟩ :=
    pt_dist_gaussian_log_tail_small c₀ c₁ ε hc₀ hc₁ hε
  refine ⟨T, hT, ?_⟩
  intro Ω _ P _ W hW n r hr
  have hsub :
      {ω | lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω)
        ((fun x : ℂ => (r : ℂ) * x) '' U)
        ((r : ℂ) * z) ((r : ℂ) * w) <
          ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} ⊆
      {ω | lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω)
        univ ((r : ℂ) * z) ((r : ℂ) * w) <
          ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} := by
    intro ω hω
    exact (pt_dist_univ_le_internal (ξ : ℝ)
      (fun y => phiMN W P 0 n y ω) _ _ _).trans_lt hω
  exact (measure_mono hsub).trans
    ((htail P W hW n r hr T hT).trans (ENNReal.ofReal_le_ofReal hsmall))

end SupercriticalLQGUniqueness.B2.DG20Pt
