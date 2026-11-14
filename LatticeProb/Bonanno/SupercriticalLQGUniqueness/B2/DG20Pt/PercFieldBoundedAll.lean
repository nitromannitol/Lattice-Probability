/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PercFieldBoundedAll at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.TailRateCompact

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem perc_field_bounded_all_of_inputs
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
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ T : ℝ, 3 < T →
        let r : ℝ := (2 : ℝ)⁻¹ ^ k
        let F : ℂ → ℂ := fun z => (r : ℂ) * z
        P {ω | crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
            (F '' U) (F '' K₁) (F '' K₂) <
          ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
            ENNReal.ofReal (T⁻¹ *
              ((2 : ℝ) ^ (-((ξ : ℝ) * Q + ζ) * (k : ℝ)) * lambdaN ξ W P n))} ≤
          ENNReal.ofReal (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2)) ∧
        P {ω | ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
            ENNReal.ofReal (T *
              ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n)) <
          crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
            (F '' U) (F '' K₁) (F '' K₂)} ≤
          ENNReal.ofReal (c₀ * Real.exp
            (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  obtain ⟨B, c₀, c₁, hB, hc₀, hc₁, hlarge⟩ :=
    perc_field_bounded_large_of_inputs hPerc hExp ξ Q hQ ζ hζ U hU
      K₁ K₂ hK₁ hK₂ hconn₁ hconn₂ hnt₁ hnt₂ hsub₁ hsub₂ hdisj hconnU
  let H : ℝ := max (9 * B) (B ^ 2)
  let c₀' : ℝ := (c₀ + 1) * Real.exp
    (c₁ * (Real.log H) ^ 2 * (1 + (Real.log (Real.log 3))⁻¹))
  have hH : 9 ≤ H := by
    dsimp [H]
    exact (by nlinarith [hB] : 9 ≤ 9 * B).trans (le_max_left _ _)
  have hc₀' : 0 < c₀' := by dsimp [c₀']; positivity
  refine ⟨c₀', c₁, hc₀', hc₁, ?_⟩
  intro Ω _ P _ W hW n k hkn T hT
  by_cases hTH : T ≤ H
  · obtain ⟨_, _, hlow, hhi⟩ := tail_rate_compact_bound c₀ c₁ H T hc₀ hc₁ hH hT hTH
    dsimp
    constructor
    · calc
        P _ ≤ (1 : ℝ≥0∞) := prob_le_one
        _ = ENNReal.ofReal 1 := by norm_num
        _ ≤ ENNReal.ofReal (c₀' * Real.exp (-c₁ * (Real.log T) ^ 2)) :=
          ENNReal.ofReal_le_ofReal hlow
    · calc
        P _ ≤ (1 : ℝ≥0∞) := prob_le_one
        _ = ENNReal.ofReal 1 := by norm_num
        _ ≤ ENNReal.ofReal (c₀' * Real.exp
            (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) :=
          ENNReal.ofReal_le_ofReal hhi
  · have hHT : H < T := lt_of_not_ge hTH
    obtain ⟨hlo, hhi⟩ := hlarge P W hW n k hkn T (by simpa only [H] using hHT)
    have hcle : c₀ ≤ c₀' := by
      obtain ⟨_, hc, _, _⟩ :=
        tail_rate_compact_bound c₀ c₁ H 4 hc₀ hc₁ hH (by norm_num) (by linarith)
      simpa only [c₀', H] using hc
    dsimp at hlo hhi ⊢
    constructor
    · exact hlo.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hcle (Real.exp_nonneg _)))
    · exact hhi.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hcle (Real.exp_nonneg _)))

end SupercriticalLQGUniqueness.B2.DG20Pt
