/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PercFieldBoundedRate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.TailRateSqrt

 





set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 



theorem perc_field_bounded_rate_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ)
    (U : Opens ℂ) (hU : Bornology.IsBounded (U : Set ℂ))
    (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hconn₁ : IsConnected K₁) (hconn₂ : IsConnected K₂)
    (hnt₁ : K₁.Nontrivial) (hnt₂ : K₂.Nontrivial)
    (hsub₁ : K₁ ⊆ U) (hsub₂ : K₂ ⊆ U)
    (hdisj : Disjoint K₁ K₂) (hconnU : IsConnected (U : Set ℂ)) :
    ∃ C c₀ c₁ d₀ d₁ : ℝ,
      0 < C ∧ 0 < c₀ ∧ 0 < c₁ ∧ 0 < d₀ ∧ 0 < d₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ T : ℝ, 9 < T →
        let r : ℝ := (2 : ℝ)⁻¹ ^ k
        let F : ℂ → ℂ := fun z => (r : ℂ) * z
        P {ω | crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
            (F '' U) (F '' K₁) (F '' K₂) <
          ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
            ENNReal.ofReal (T⁻¹ * (C⁻¹ *
              (2 : ℝ) ^ (-((ξ : ℝ) * Q + ζ) * (k : ℝ)) *
                lambdaN ξ W P n))} ≤
          ENNReal.ofReal ((d₀ + c₀) * Real.exp
            (-(min d₁ c₁ / 4) * (Real.log T) ^ 2)) ∧
        P {ω | ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
            ENNReal.ofReal (T * (C *
              (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) *
                lambdaN ξ W P n)) <
          crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
            (F '' U) (F '' K₁) (F '' K₂)} ≤
          ENNReal.ofReal ((d₀ + c₀) * Real.exp
            (-(min (d₁ * Real.log (Real.log 3)) c₁ / 4) *
              (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  obtain ⟨C, c₀, c₁, d₀, d₁, hC, hc₀, hc₁, hd₀, hd₁, hbefore⟩ :=
    perc_field_bounded_sqrt_of_inputs hPerc hExp ξ Q hQ ζ hζ U hU
      K₁ K₂ hK₁ hK₂ hconn₁ hconn₂ hnt₁ hnt₂ hsub₁ hsub₂ hdisj hconnU
  refine ⟨C, c₀, c₁, d₀, d₁, hC, hc₀, hc₁, hd₀, hd₁, ?_⟩
  intro Ω _ P _ W hW n k hkn T hT
  obtain ⟨hlo, hhi⟩ := hbefore P W hW n k hkn T hT
  dsimp at hlo hhi ⊢
  constructor
  · exact hlo.trans (gaussian_sum_sqrt_bound c₀ c₁ d₀ d₁ T hc₀ hd₀ hT)
  · exact hhi.trans (gaussian_loglog_sum_sqrt_bound
      c₀ c₁ d₀ d₁ T hc₀ hc₁ hd₀ hd₁ hT)

end SupercriticalLQGUniqueness.B2.DG20Pt
