/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PercFieldBefore at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PercBandTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.CoarseOscLog
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.FieldTailSplit

 





set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 




theorem perc_field_before_of_percEstimate
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (U : Opens ℂ) (hU : Bornology.IsBounded (U : Set ℂ))
    (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hconn₁ : IsConnected K₁) (hconn₂ : IsConnected K₂)
    (hnt₁ : K₁.Nontrivial) (hnt₂ : K₂.Nontrivial)
    (hsub₁ : K₁ ⊆ U) (hsub₂ : K₂ ⊆ U)
    (hdisj : Disjoint K₁ K₂) (hconnU : IsConnected (U : Set ℂ)) :
    ∃ c₀ c₁ d₀ d₁ : ℝ,
      0 < c₀ ∧ 0 < c₁ ∧ 0 < d₀ ∧ 0 < d₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ T : ℝ, 3 < T →
        let r : ℝ := (2 : ℝ)⁻¹ ^ k
        let F : ℂ → ℂ := fun z => (r : ℂ) * z
        let δ : ℝ := Real.log T / (2 * (ξ : ℝ))
        P {ω | ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * δ)) *
          crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
            (F '' U) (F '' K₁) (F '' K₂) <
          ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
            (ENNReal.ofReal r *
              ENNReal.ofReal (T⁻¹ * lambdaN ξ W P (n - k)))} ≤
            ENNReal.ofReal (d₀ * Real.exp (-d₁ * (Real.log T) ^ 2)) +
              ENNReal.ofReal (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2)) ∧
        P {ω | ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * δ)) *
          (ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
            (ENNReal.ofReal r *
              ENNReal.ofReal (T * lambdaN ξ W P (n - k)))) <
          crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
            (F '' U) (F '' K₁) (F '' K₂)} ≤
            ENNReal.ofReal (d₀ * Real.exp (-d₁ * (Real.log T) ^ 2)) +
              ENNReal.ofReal (c₀ * Real.exp
                (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  obtain ⟨c₀, c₁, hc₀, hc₁, hband⟩ :=
    perc_band_tails_of_percEstimate hPerc ξ U K₁ K₂ hK₁ hK₂ hconn₁ hconn₂
      hnt₁ hnt₂ hsub₁ hsub₂ hdisj hconnU
  obtain ⟨d₀, d₁, hd₀, hd₁, hosc⟩ :=
    phiMN_center_osc_log_tail hU ξ ξ.property
  refine ⟨c₀, c₁, d₀, d₁, hc₀, hc₁, hd₀, hd₁, ?_⟩
  intro Ω _ P _ W hW n k hkn T hT
  dsimp
  let r : ℝ := (2 : ℝ)⁻¹ ^ k
  let F : ℂ → ℂ := fun z => (r : ℂ) * z
  let δ : ℝ := Real.log T / (2 * (ξ : ℝ))
  have hosc' : P {ω | ∃ z ∈ F '' U,
      δ < |phiMN W P 0 k z ω - phiMN W P 0 k 0 ω|} ≤
      ENNReal.ofReal (d₀ * Real.exp (-d₁ * (Real.log T) ^ 2)) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (by simpa only [F, r, δ] using hosc P W hW k T hT)
  obtain ⟨hbandlo, hbandhi⟩ := hband P W hW n k hkn T hT
  rw [measure_band_crossing_open_lt P W hW ξ U K₁ K₂ hkn] at hbandlo
  rw [measure_band_crossing_open_gt P W hW ξ U K₁ K₂ hkn] at hbandhi
  constructor
  · exact (measure_full_crossing_lt_split P W hW ξ U K₁ K₂ hkn δ
      (ENNReal.ofReal (T⁻¹ * lambdaN ξ W P (n - k)))).trans
        (add_le_add hosc' hbandlo)
  · exact (measure_full_crossing_gt_split P W hW ξ U K₁ K₂ hkn δ
      (ENNReal.ofReal (T * lambdaN ξ W P (n - k)))).trans
        (add_le_add hosc' hbandhi)

end SupercriticalLQGUniqueness.B2.DG20Pt
