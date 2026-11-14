/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAroundScale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NormalizerBandScale

 





set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 
theorem hasAroundLoop_mono {ξ : ℝ} {φ : ℂ → ℝ} {x : ℂ}
    {r : ℝ} {hr : 0 < r} {A B : ℝ≥0∞} (hAB : A ≤ B)
    (h : Inputs.HasAroundLoop ξ φ x r hr A) :
    Inputs.HasAroundLoop ξ φ x r hr B := by
  obtain ⟨γ, a, b, hγ, hann, hsep, hlen⟩ := h
  exact ⟨γ, a, b, hγ, hann, hsep, hlen.trans_le hAB⟩

 



theorem around_scale_upper_of_inputs
    (hAround : Inputs.DG20AroundEstimate)
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ C c₀ c₁ : ℝ, 0 < C ∧ 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ x : ℂ,
          ∀ T : ℝ, 3 < T →
          let r : ℝ := ((2 : ℝ)⁻¹) ^ k
          P {ω | ¬ Inputs.HasAroundLoop (ξ : ℝ)
                (fun z => phiMN W P 0 n z ω) x r
                (by dsimp [r]; positivity)
                (ENNReal.ofReal (T * (C *
                  (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) *
                    lambdaN (ξ : ℝ) W P n) *
                  Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω)))} ≤
            ENNReal.ofReal (c₀ * Real.exp
              (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  obtain ⟨C, hC, hScale⟩ :=
    normalizer_band_scale_of_exponentRelation hExp ξ Q hQ ζ hζ
  obtain ⟨c₀, c₁, hc₀, hc₁, hTail⟩ := hAround ξ
  refine ⟨C, c₀, c₁, hC, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW n k hkn x T hT
  have hscale := (hScale P W hW n k hkn).2
  have hT0 : 0 ≤ T := by linarith
  have hsub :
      {ω | ¬ Inputs.HasAroundLoop (ξ : ℝ)
        (fun z => phiMN W P 0 n z ω) x (((2 : ℝ)⁻¹) ^ k)
        (by positivity)
        (ENNReal.ofReal (T * (C *
          (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) *
            lambdaN (ξ : ℝ) W P n) *
          Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω)))} ⊆
      {ω | ¬ Inputs.HasAroundLoop (ξ : ℝ)
        (fun z => phiMN W P 0 n z ω) x (((2 : ℝ)⁻¹) ^ k)
        (by positivity)
        (ENNReal.ofReal (T * (((2 : ℝ)⁻¹) ^ k) *
          lambdaN (ξ : ℝ) W P (n - k) *
          Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω)))} := by
    intro ω hbad hgood
    apply hbad
    apply hasAroundLoop_mono ?_ hgood
    apply ENNReal.ofReal_le_ofReal
    have hscale' := mul_le_mul_of_nonneg_left hscale hT0
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hscale'
        (Real.exp_nonneg ((ξ : ℝ) * phiMN W P 0 k x ω))
  exact (measure_mono hsub).trans (hTail P W hW n k hkn x T hT)

end SupercriticalLQGUniqueness.B2.DG20Pt
