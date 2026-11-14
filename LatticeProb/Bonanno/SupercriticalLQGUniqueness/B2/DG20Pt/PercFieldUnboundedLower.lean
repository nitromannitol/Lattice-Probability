/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PercFieldUnboundedLower at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.FiniteBoxesLowerTail

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem perc_field_lower_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ)
    (U : Opens ℂ) (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (_hconn₁ : IsConnected K₁) (_hconn₂ : IsConnected K₂)
    (_hnt₁ : K₁.Nontrivial) (_hnt₂ : K₂.Nontrivial)
    (hsub₁ : K₁ ⊆ U) (_hsub₂ : K₂ ⊆ U)
    (hdisj : Disjoint K₁ K₂) (_hconnU : IsConnected (U : Set ℂ)) :
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
          ENNReal.ofReal (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2)) := by
  obtain ⟨ρ, hρ, F, hbarrier⟩ :=
    exists_scaled_finite_box_cross_lower U K₁ K₂ hK₁ hK₂ hsub₁ hdisj
  obtain ⟨c₀, c₁, hc₀, hc₁, hboxes⟩ :=
    perc_field_finite_boxes_lower_of_inputs hPerc hExp ξ Q hQ ζ hζ ρ hρ F
  refine ⟨c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW n k hkn T hT
  let r : ℝ := (2 : ℝ)⁻¹ ^ k
  have hr : 0 < r := by dsimp [r]; positivity
  have hbox := hboxes P W hW n k hkn T hT
  dsimp at hbox ⊢
  apply (measure_mono ?_).trans hbox
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact lt_of_le_of_lt
    (hbarrier (ξ : ℝ) (fun z => phiMN W P 0 n z ω) r hr) hω

end SupercriticalLQGUniqueness.B2.DG20Pt

