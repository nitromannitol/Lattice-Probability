/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatLambdaRealPair at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatLambdaDyadicPair
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatDyadicPairGeometry
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28U1Aux
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Thm11

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_lambda_delta_real_pair_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W →
        ∀ δ₁ δ₂ : Ioo (0 : ℝ) 1, (δ₁ : ℝ) < (δ₂ : ℝ) →
          B⁻¹ * (C⁻¹ *
            ((2 : ℝ) ^ (-|1 - (ξ : ℝ) * Q + ζ|) *
              ((δ₁ : ℝ) / (δ₂ : ℝ)) ^ (1 - (ξ : ℝ) * Q + ζ) *
              lambdaDelta ξ W P δ₂)) ≤
              lambdaDelta ξ W P δ₁ ∧
          lambdaDelta ξ W P δ₁ ≤
            B * (C *
              ((2 : ℝ) ^ |1 - (ξ : ℝ) * Q - ζ| *
                ((δ₁ : ℝ) / (δ₂ : ℝ)) ^ (1 - (ξ : ℝ) * Q - ζ) *
                lambdaDelta ξ W P δ₂)) := by
  obtain ⟨C, B, hC, hB, hpair⟩ :=
    dg20_lambda_delta_dyadic_pair_of_inputs hPerc hExp ξ Q hQ ζ hζ
  refine ⟨C, B, hC, hB, ?_⟩
  intro Ω _ P _ W hW δ₁ δ₂ hδ
  obtain ⟨n₁, s₁, hs₁, hs₁', hrepr₁⟩ :=
    S6P28U.exists_split' δ₁.property.1 δ₁.property.2
  obtain ⟨n₂, s₂, hs₂, hs₂', hrepr₂⟩ :=
    S6P28U.exists_split' δ₂.property.1 δ₂.property.2
  have hgeom := dg20_dyadic_pair_geometry n₁ n₂ s₁ s₂ δ₁ δ₂
    hs₁ hs₁' hs₂ hs₂' hrepr₁ hrepr₂ hδ
  let t : ℝ := (δ₁ : ℝ) / (δ₂ : ℝ)
  let aLo : ℝ := 1 - (ξ : ℝ) * Q + ζ
  let aHi : ℝ := 1 - (ξ : ℝ) * Q - ζ
  have hpLo := dg20_dyadic_power_compare (n₁ - n₂)
    s₁ s₂ aLo t hs₁.le hs₁' hs₂.le hs₂' hgeom.2
  have hpHi := dg20_dyadic_power_compare (n₁ - n₂)
    s₁ s₂ aHi t hs₁.le hs₁' hs₂.le hs₂' hgeom.2
  obtain ⟨hlo, hhi⟩ := hpair P W hW n₁ n₂ hgeom.1
    s₁ s₂ hs₁.le hs₁' hs₂.le hs₂'
  rw [← hrepr₁, ← hrepr₂] at hlo hhi
  have hδ₂pos : 0 < lambdaDelta ξ W P δ₂ :=
    S6Thm.lambdaDelta_pos_of_698 hW
      (dg20_non_dyadic_median_compare_of_perc hPerc ξ P W hW)
      δ₂.property
  constructor
  · calc
      B⁻¹ * (C⁻¹ * ((2 : ℝ) ^ (-|1 - (ξ : ℝ) * Q + ζ|) *
        t ^ aLo * lambdaDelta ξ W P δ₂)) ≤
          B⁻¹ * (C⁻¹ * ((2 : ℝ) ^ (-aLo * ((n₁ - n₂ : ℕ) : ℝ)) *
            lambdaDelta ξ W P δ₂)) := by
        have hpow : (2 : ℝ) ^ (-|1 - (ξ : ℝ) * Q + ζ|) * t ^ aLo ≤
            (2 : ℝ) ^ (-aLo * ((n₁ - n₂ : ℕ) : ℝ)) := by
          simpa only [aLo] using hpLo.1
        gcongr
      _ ≤ lambdaDelta ξ W P δ₁ := by
        simpa only [aLo, t, mul_assoc] using hlo
  · calc
      lambdaDelta ξ W P δ₁ ≤
          B * (C * ((2 : ℝ) ^ (-aHi * ((n₁ - n₂ : ℕ) : ℝ)) *
            lambdaDelta ξ W P δ₂)) := by
        simpa only [aHi, t, mul_assoc] using hhi
      _ ≤ B * (C * ((2 : ℝ) ^ |1 - (ξ : ℝ) * Q - ζ| *
            t ^ aHi * lambdaDelta ξ W P δ₂)) := by
        have hpow : (2 : ℝ) ^ (-aHi * ((n₁ - n₂ : ℕ) : ℝ)) ≤
            (2 : ℝ) ^ |1 - (ξ : ℝ) * Q - ζ| * t ^ aHi := by
          simpa only [aHi] using hpHi.2
        gcongr

end SupercriticalLQGUniqueness.B2.DG20Pt
