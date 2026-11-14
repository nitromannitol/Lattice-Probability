/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatNormalizerGlobalCompare at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatLambdaRealPair
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatMedianCompare
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatNormalizerAwayZero
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatRpowInterval

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_median_white_noise_compare_all_scales_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ G : ℝ, 0 < G ∧
      ∀ ε : Ioo (0 : ℝ) 1,
        ∀ {Ω' : Type} [MeasurableSpace Ω'] (R : Measure Ω')
          [IsProbabilityMeasure R] (W : WNSpace → Ω' → ℝ),
          IsWhiteNoise R W →
          G⁻¹ * lambdaDelta ξ W R ε ≤ (m ⟨ε, ε.property.1⟩ : ℝ) ∧
          (m ⟨ε, ε.property.1⟩ : ℝ) ≤ G * lambdaDelta ξ W R ε := by
  obtain ⟨A, ε₀, hA, hε₀, hsmall⟩ :=
    dg20_heat_median_white_noise_compare_of_perc hPerc ξ m hm P h hh X hX
  let δ₀r : ℝ := min (ε₀ / 2) (1 / 2)
  have hδ₀pos : 0 < δ₀r := lt_min (half_pos hε₀) (by norm_num)
  have hδ₀one : δ₀r < 1 :=
    (min_le_right _ _).trans_lt (by norm_num)
  have hδ₀small : δ₀r < ε₀ :=
    (min_le_left _ _).trans_lt (half_lt_self hε₀)
  let δ₀ : Ioo (0 : ℝ) 1 := ⟨δ₀r, hδ₀pos, hδ₀one⟩
  obtain ⟨cm, Cm, hcm, hCm, hcompact⟩ :=
    dg20_heat_normalizer_bounds_away_zero ξ m hm P h hh X hX
      ε₀ hε₀
  obtain ⟨C, B, hC, hB, hpair⟩ :=
    dg20_lambda_delta_real_pair_of_inputs hPerc hExp ξ Q hQ ζ hζ
  let aLo : ℝ := 1 - (ξ : ℝ) * Q + ζ
  let aHi : ℝ := 1 - (ξ : ℝ) * Q - ζ
  let dLo : ℝ := B⁻¹ * (C⁻¹ *
    ((2 : ℝ) ^ (-|aLo|) * δ₀r ^ |aLo|))
  let dHi : ℝ := B * (C *
    ((2 : ℝ) ^ |aHi| * δ₀r ^ (-|aHi|)))
  have hdLo : 0 < dLo := by dsimp [dLo]; positivity
  have hdHi : 0 < dHi := by dsimp [dHi]; positivity
  let m₀ : ℝ := (m ⟨δ₀r, hδ₀pos⟩ : ℝ)
  have hm₀ : 0 < m₀ := (m ⟨δ₀r, hδ₀pos⟩).property
  let G : ℝ := max A (max (A * m₀ / (dLo * cm))
    (Cm * A * dHi / m₀))
  have hG : 0 < G := lt_of_lt_of_le hA (le_max_left _ _)
  refine ⟨G, hG, ?_⟩
  intro ε Ω' _ R _ W hW
  have hLamPos : 0 < lambdaDelta ξ W R ε :=
    S6Thm.lambdaDelta_pos_of_698 hW
      (dg20_non_dyadic_median_compare_of_perc hPerc ξ R W hW)
      ε.property
  by_cases hε : (ε : ℝ) < ε₀
  · obtain ⟨hlo, hhi⟩ := hsmall ε hε R W hW
    constructor
    · calc
        G⁻¹ * lambdaDelta ξ W R ε ≤
            A⁻¹ * lambdaDelta ξ W R ε := by
          exact mul_le_mul_of_nonneg_right
            (by simpa only [one_div] using
              one_div_le_one_div_of_le hA (le_max_left A _)) hLamPos.le
        _ ≤ (m ⟨ε, ε.property.1⟩ : ℝ) := hlo
    · exact hhi.trans (mul_le_mul_of_nonneg_right
        (le_max_left A _) hLamPos.le)
  · have hε₀le : ε₀ ≤ (ε : ℝ) := le_of_not_gt hε
    obtain ⟨hmlo, hmhi⟩ := hcompact ε hε₀le
    have hδ₀ε : (δ₀ : ℝ) < (ε : ℝ) :=
      hδ₀small.trans_le hε₀le
    have htpos : 0 < δ₀r / (ε : ℝ) :=
      div_pos hδ₀pos ε.property.1
    have htlo : δ₀r ≤ δ₀r / (ε : ℝ) := by
      apply (le_div_iff₀ ε.property.1).2
      exact mul_le_of_le_one_right hδ₀pos.le ε.property.2.le
    have hthi : δ₀r / (ε : ℝ) ≤ 1 := by
      exact (div_le_iff₀ ε.property.1).2
        (by simpa only [one_mul] using hδ₀ε.le)
    obtain ⟨hpLo, _⟩ :=
      dg20_rpow_interval_bounds hδ₀pos htlo hthi (a := aLo)
    obtain ⟨_, hpHi⟩ :=
      dg20_rpow_interval_bounds hδ₀pos htlo hthi (a := aHi)
    obtain ⟨hLamLo, hLamHi⟩ := hpair R W hW δ₀ ε hδ₀ε
    have hLam0Lo : dLo * lambdaDelta ξ W R ε ≤
        lambdaDelta ξ W R δ₀ := by
      apply le_trans ?_ hLamLo
      have hpow : (2 : ℝ) ^ (-|aLo|) * δ₀r ^ |aLo| ≤
          (2 : ℝ) ^ (-|aLo|) * (δ₀r / (ε : ℝ)) ^ aLo := by
        exact mul_le_mul_of_nonneg_left hpLo (by positivity)
      have hmul := mul_le_mul_of_nonneg_right hpow hLamPos.le
      have hCmul := mul_le_mul_of_nonneg_left hmul (inv_pos.mpr hC).le
      have hBmul := mul_le_mul_of_nonneg_left hCmul (inv_pos.mpr hB).le
      simpa only [dLo, aLo, δ₀, mul_assoc] using hBmul
    have hLam0Hi : lambdaDelta ξ W R δ₀ ≤
        dHi * lambdaDelta ξ W R ε := by
      apply le_trans hLamHi
      have hpow : (2 : ℝ) ^ |aHi| *
          (δ₀r / (ε : ℝ)) ^ aHi ≤
          (2 : ℝ) ^ |aHi| * δ₀r ^ (-|aHi|) := by
        exact mul_le_mul_of_nonneg_left hpHi (by positivity)
      have hmul := mul_le_mul_of_nonneg_right hpow hLamPos.le
      have hCmul := mul_le_mul_of_nonneg_left hmul hC.le
      have hBmul := mul_le_mul_of_nonneg_left hCmul hB.le
      simpa only [dHi, aHi, δ₀, mul_assoc] using hBmul
    obtain ⟨hLam0Mlo, hmLam0Hi⟩ := hsmall δ₀ hδ₀small R W hW
    have hLam0BoundLo : m₀ / A ≤ lambdaDelta ξ W R δ₀ := by
      apply (div_le_iff₀ hA).2
      nlinarith [hmLam0Hi]
    have hLam0BoundHi : lambdaDelta ξ W R δ₀ ≤ A * m₀ := by
      have htmp : lambdaDelta ξ W R δ₀ / A ≤ m₀ := by
        simpa only [m₀, δ₀, inv_mul_eq_div] using hLam0Mlo
      simpa only [mul_comm] using (div_le_iff₀ hA).1 htmp
    have hGl : A * m₀ / (dLo * cm) ≤ G :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hGh : Cm * A * dHi / m₀ ≤ G :=
      (le_max_right _ _).trans (le_max_right _ _)
    constructor
    · rw [inv_mul_eq_div]
      apply (div_le_iff₀ hG).2
      calc
        lambdaDelta ξ W R ε ≤ A * m₀ / dLo := by
          apply (le_div_iff₀ hdLo).2
          nlinarith [hLam0Lo, hLam0BoundHi]
        _ = (A * m₀ / (dLo * cm)) * cm := by
          field_simp
        _ ≤ G * cm := mul_le_mul_of_nonneg_right hGl hcm.le
        _ ≤ G * (m ⟨ε, ε.property.1⟩ : ℝ) :=
          mul_le_mul_of_nonneg_left hmlo hG.le
        _ = (m ⟨ε, ε.property.1⟩ : ℝ) * G := mul_comm _ _
    · calc
        (m ⟨ε, ε.property.1⟩ : ℝ) ≤ Cm := hmhi
        _ = (Cm * A * dHi / m₀) * (m₀ / (A * dHi)) := by
          field_simp
        _ ≤ G * (m₀ / (A * dHi)) :=
          mul_le_mul_of_nonneg_right hGh (by positivity)
        _ ≤ G * lambdaDelta ξ W R ε := by
          apply mul_le_mul_of_nonneg_left ?_ hG.le
          apply (div_le_iff₀ (mul_pos hA hdHi)).2
          nlinarith [hLam0Hi, hLam0BoundLo]

end SupercriticalLQGUniqueness.B2.DG20Pt
