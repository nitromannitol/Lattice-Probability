/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PercFieldNormalizedBefore at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PercFieldBefore
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NormalizerBandScale

 





set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 




theorem perc_field_normalized_before_of_inputs
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
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ T : ℝ, 3 < T →
        let r : ℝ := (2 : ℝ)⁻¹ ^ k
        let F : ℂ → ℂ := fun z => (r : ℂ) * z
        let δ : ℝ := Real.log T / (2 * (ξ : ℝ))
        P {ω | ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * δ)) *
          crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
            (F '' U) (F '' K₁) (F '' K₂) <
          ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
            ENNReal.ofReal (T⁻¹ * (C⁻¹ *
              (2 : ℝ) ^ (-((ξ : ℝ) * Q + ζ) * (k : ℝ)) *
                lambdaN ξ W P n))} ≤
          ENNReal.ofReal (d₀ * Real.exp (-d₁ * (Real.log T) ^ 2)) +
            ENNReal.ofReal (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2)) ∧
        P {ω | ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * δ)) *
          (ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
            ENNReal.ofReal (T * (C *
              (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) *
                lambdaN ξ W P n))) <
          crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
            (F '' U) (F '' K₁) (F '' K₂)} ≤
          ENNReal.ofReal (d₀ * Real.exp (-d₁ * (Real.log T) ^ 2)) +
            ENNReal.ofReal (c₀ * Real.exp
              (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  obtain ⟨C, hC, hscale⟩ :=
    normalizer_band_scale_of_exponentRelation
      (show DG20ExponentRelation from hExp) ξ Q hQ ζ hζ
  obtain ⟨c₀, c₁, d₀, d₁, hc₀, hc₁, hd₀, hd₁, hbefore⟩ :=
    perc_field_before_of_percEstimate hPerc ξ U hU K₁ K₂ hK₁ hK₂
      hconn₁ hconn₂ hnt₁ hnt₂ hsub₁ hsub₂ hdisj hconnU
  refine ⟨C, c₀, c₁, d₀, d₁, hC, hc₀, hc₁, hd₀, hd₁, ?_⟩
  intro Ω _ P _ W hW n k hkn T hT
  obtain ⟨hlo, hhi⟩ := hscale P W hW n k hkn
  obtain ⟨hbeforeLo, hbeforeHi⟩ := hbefore P W hW n k hkn T hT
  dsimp at hbeforeLo hbeforeHi ⊢
  let r : ℝ := (2 : ℝ)⁻¹ ^ k
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hT0 : 0 ≤ T := by linarith
  have hTi : 0 ≤ T⁻¹ := inv_nonneg.mpr hT0
  have hthresholdLo :
      ENNReal.ofReal (T⁻¹ * (C⁻¹ *
          (2 : ℝ) ^ (-((ξ : ℝ) * Q + ζ) * (k : ℝ)) * lambdaN ξ W P n)) ≤
        ENNReal.ofReal r * ENNReal.ofReal (T⁻¹ * lambdaN ξ W P (n - k)) := by
    rw [← ENNReal.ofReal_mul hr]
    apply ENNReal.ofReal_le_ofReal
    calc
      T⁻¹ * (C⁻¹ * (2 : ℝ) ^ (-((ξ : ℝ) * Q + ζ) * (k : ℝ)) *
          lambdaN ξ W P n) ≤ T⁻¹ * (r * lambdaN ξ W P (n - k)) :=
        mul_le_mul_of_nonneg_left (by simpa only [r] using hlo) hTi
      _ = r * (T⁻¹ * lambdaN ξ W P (n - k)) := by ring
  have hthresholdHi :
      ENNReal.ofReal r * ENNReal.ofReal (T * lambdaN ξ W P (n - k)) ≤
        ENNReal.ofReal (T * (C *
          (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n)) := by
    rw [← ENNReal.ofReal_mul hr]
    apply ENNReal.ofReal_le_ofReal
    calc
      r * (T * lambdaN ξ W P (n - k)) =
          T * (r * lambdaN ξ W P (n - k)) := by ring
      _ ≤ T * (C * (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) *
          lambdaN ξ W P n) :=
        mul_le_mul_of_nonneg_left (by simpa only [r] using hhi) hT0
  constructor
  · apply (measure_mono ?_).trans hbeforeLo
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    apply lt_of_lt_of_le hω
    gcongr
  · apply (measure_mono ?_).trans hbeforeHi
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    apply lt_of_le_of_lt _ hω
    gcongr

end SupercriticalLQGUniqueness.B2.DG20Pt
