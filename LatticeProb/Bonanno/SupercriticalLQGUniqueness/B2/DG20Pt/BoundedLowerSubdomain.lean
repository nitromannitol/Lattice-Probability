/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.BoundedLowerSubdomain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.BoxSideGeom
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PercFieldBoundedAll

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem perc_field_compact_subdomain_lower_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ)
    (U : Opens ℂ) (hU : Bornology.IsBounded (U : Set ℂ))
    (hconnU : IsConnected (U : Set ℂ))
    (K A B : Set ℂ) (hKU : K ⊆ U)
    (hAK : A ⊆ K) (hBK : B ⊆ K)
    (hA : IsCompact A) (hB : IsCompact B)
    (hconnA : IsConnected A) (hconnB : IsConnected B)
    (hntA : A.Nontrivial) (hntB : B.Nontrivial)
    (hdisj : Disjoint A B) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ T : ℝ, 3 < T →
        let r : ℝ := (2 : ℝ)⁻¹ ^ k
        let F : ℂ → ℂ := fun z => (r : ℂ) * z
        P {ω | crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
            (F '' K) (F '' A) (F '' B) <
          ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
            ENNReal.ofReal (T⁻¹ *
              ((2 : ℝ) ^ (-((ξ : ℝ) * Q + ζ) * (k : ℝ)) * lambdaN ξ W P n))} ≤
          ENNReal.ofReal (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2)) := by
  obtain ⟨c₀, c₁, hc₀, hc₁, hbound⟩ :=
    perc_field_bounded_all_of_inputs hPerc hExp ξ Q hQ ζ hζ
      U hU A B hA hB hconnA hconnB hntA hntB
      (hAK.trans hKU) (hBK.trans hKU) hdisj hconnU
  refine ⟨c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW n k hkn T hT
  have hlo := (hbound P W hW n k hkn T hT).1
  dsimp at hlo ⊢
  apply (measure_mono ?_).trans hlo
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact lt_of_le_of_lt (crossLenIn_mono_domain (ξ : ℝ)
    (fun z => phiMN W P 0 n z ω) (Set.image_mono hKU)) hω

end SupercriticalLQGUniqueness.B2.DG20Pt
