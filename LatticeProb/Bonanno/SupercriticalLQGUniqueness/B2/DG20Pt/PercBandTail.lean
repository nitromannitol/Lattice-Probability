/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PercBandTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.Inputs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.BandTailLaw

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 




theorem perc_band_tails_of_percEstimate
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (U : Opens ℂ) (K₁ K₂ : Set ℂ)
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
        P {ω | crossLenIn (ξ : ℝ) (fun z => phiMN W P k n z ω)
            (F '' U) (F '' K₁) (F '' K₂) <
              ENNReal.ofReal r * ENNReal.ofReal (T⁻¹ * lambdaN ξ W P (n - k))} ≤
          ENNReal.ofReal (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2)) ∧
        P {ω | ENNReal.ofReal r * ENNReal.ofReal (T * lambdaN ξ W P (n - k)) <
            crossLenIn (ξ : ℝ) (fun z => phiMN W P k n z ω)
              (F '' U) (F '' K₁) (F '' K₂)} ≤
          ENNReal.ofReal (c₀ * Real.exp
            (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  obtain ⟨c₀, c₁, hc₀, hc₁, htail⟩ :=
    hPerc ξ U K₁ K₂ hK₁ hK₂ hconn₁ hconn₂ hnt₁ hnt₂ hsub₁ hsub₂ hdisj hconnU
  refine ⟨c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW n k hkn T hT
  obtain ⟨hlower, hupper⟩ := htail P W hW (n - k) T hT
  dsimp
  constructor
  · rw [measure_band_crossing_open_lt P W hW ξ U K₁ K₂ hkn]
    exact hlower
  · rw [measure_band_crossing_open_gt P W hW ξ U K₁ K₂ hkn]
    exact hupper

end SupercriticalLQGUniqueness.B2.DG20Pt
