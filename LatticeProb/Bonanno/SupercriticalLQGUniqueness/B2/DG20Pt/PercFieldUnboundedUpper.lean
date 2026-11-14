/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PercFieldUnboundedUpper at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PercFieldBoundedAll
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_1Geom

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace Metric
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 



theorem perc_field_upper_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ)
    (U : Opens ℂ) (K₁ K₂ : Set ℂ)
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
        P {ω | ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
            ENNReal.ofReal (T *
              ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n)) <
          crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
            (F '' U) (F '' K₁) (F '' K₂)} ≤
          ENNReal.ofReal (c₀ * Real.exp
            (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  obtain ⟨U₀, R₀, _hR₀, hU₀open, hU₀conn, hU₀R, hK₁U₀, hK₂U₀, hU₀U⟩ :=
    LQGMetric.DFGPS.P31.exists_bounded_conn U.isOpen hconnU
      hK₁ hconn₁ hK₂ hconn₂ hsub₁ hsub₂
  let U₀' : Opens ℂ := ⟨U₀, hU₀open⟩
  have hU₀bounded : Bornology.IsBounded (U₀' : Set ℂ) :=
    (isBounded_iff_subset_ball (0 : ℂ)).2 ⟨R₀, hU₀R⟩
  obtain ⟨c₀, c₁, hc₀, hc₁, hbound⟩ :=
    perc_field_bounded_all_of_inputs hPerc hExp ξ Q hQ ζ hζ
      U₀' hU₀bounded K₁ K₂ hK₁ hK₂ hconn₁ hconn₂ hnt₁ hnt₂
      hK₁U₀ hK₂U₀ hdisj hU₀conn
  refine ⟨c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW n k hkn T hT
  have hupper := (hbound P W hW n k hkn T hT).2
  dsimp at hupper ⊢
  apply (measure_mono ?_).trans hupper
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact lt_of_lt_of_le hω (crossLenIn_mono_domain (ξ : ℝ)
    (fun z => phiMN W P 0 n z ω) (Set.image_mono hU₀U))

end SupercriticalLQGUniqueness.B2.DG20Pt
