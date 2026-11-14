/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3Base at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3PhiUpper
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBX0Window

 







set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 

theorem laneB3_phi_lower_tail_base (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ A a T₀ : ℝ, 0 < A ∧ 0 < a ∧ 1 < T₀ ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ (K : ℕ) (T : ℝ), T₀ ≤ T →
        P {ω | lenObs (ξ : ℝ) (phiMN W P 0 K) (rectAB 1 1) ω <
          T⁻¹ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (K : ℝ)) * lambdaN (ξ : ℝ) W P 0} ≤
          ENNReal.ofReal (A * Real.exp (-a * (Real.log T) ^ 2)) := by
  obtain ⟨pa, ca, Ca, Cna, cna, Cpa, cpa, hpa, hpaH, hca, hCa, hCna, hcna, hCpa, hcpa,
    hapr⟩ := laneB_apriori_unit_square_power_tails ξ Q hQ ζ hζ
  obtain ⟨c0, C0, hc0, hC0, hwin⟩ := laneB_whiteNoise_median_window ξ Q hQ ζ hζ
  set y₀ : ℝ := 2 * (Real.log 3 + |Real.log ca| + |Real.log C0| + |Real.log Ca|) + 1 with hy₀
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h1 := abs_nonneg (Real.log ca)
  have h2 := abs_nonneg (Real.log C0)
  have h3 := abs_nonneg (Real.log Ca)
  have hy₀1 : 1 ≤ y₀ := by rw [hy₀]; linarith
  refine ⟨Cna, cna / 4, Real.exp y₀, hCna, by positivity,
    by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith), ?_⟩
  intro Ω _ P W hW K T hT
  have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT
  set y : ℝ := Real.log T with hydef
  have hyy₀ : y₀ ≤ y := by rw [hydef, Real.le_log_iff_exp_le hTpos]; exact hT
  set T' : ℝ := T / C0 with hT'
  have hT'pos : 0 < T' := div_pos hTpos hC0
  have hlogT' : Real.log T' = y - Real.log C0 := by rw [hT', Real.log_div hTpos.ne' hC0.ne']
  have hcaT : 3 < ca * T' := by
    rw [← Real.exp_log (mul_pos hca hT'pos), ← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    refine Real.exp_lt_exp.mpr ?_
    rw [Real.log_mul hca.ne' hT'pos.ne', hlogT']
    have := neg_abs_le (Real.log ca); have := le_abs_self (Real.log C0); linarith
  have hTCa : 3 < T' / Ca := by
    rw [← Real.exp_log (div_pos hT'pos hCa), ← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    refine Real.exp_lt_exp.mpr ?_
    rw [Real.log_div hT'pos.ne' hCa.ne', hlogT']
    have := le_abs_self (Real.log Ca); have := le_abs_self (Real.log C0); linarith
  have hlam : lambdaN (ξ : ℝ) W P 0 ≤ C0 := by
    have := (hwin P W hW 0).2; simpa using this
  have hsub : {ω | lenObs (ξ : ℝ) (phiMN W P 0 K) (rectAB 1 1) ω <
      T⁻¹ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (K : ℝ)) * lambdaN (ξ : ℝ) W P 0} ⊆
      {ω | lenObs (ξ : ℝ) (phiMN W P 0 K) (rectAB 1 1) ω <
        T'⁻¹ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (K : ℝ))} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    refine lt_of_lt_of_le hω ?_
    have hg : 0 ≤ (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (K : ℝ)) := by positivity
    have : T'⁻¹ = T⁻¹ * C0 := by rw [hT', inv_div, div_eq_inv_mul]
    rw [this]
    have hTi : 0 ≤ T⁻¹ := inv_nonneg.mpr hTpos.le
    calc T⁻¹ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (K : ℝ)) * lambdaN (ξ : ℝ) W P 0
        ≤ T⁻¹ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (K : ℝ)) * C0 :=
          mul_le_mul_of_nonneg_left hlam (mul_nonneg hTi hg)
      _ = T⁻¹ * C0 * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (K : ℝ)) := by ring
  refine (measure_mono hsub).trans (((hapr P W hW K T' hcaT hTCa).1).trans ?_)
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCna.le)
  have hlo : y / 2 ≤ Real.log (ca * T') := by
    rw [Real.log_mul hca.ne' hT'pos.ne', hlogT']
    have := neg_abs_le (Real.log ca); have := le_abs_self (Real.log C0); linarith
  have hsq : (y / 2) ^ 2 ≤ (Real.log (ca * T')) ^ 2 := pow_le_pow_left₀ (by linarith) hlo 2
  have h4 := mul_le_mul_of_nonneg_left hsq hcna.le
  have e : cna * (y / 2) ^ 2 = cna / 4 * y ^ 2 := by ring
  linarith

 

theorem laneB3_phi_upper_tail_base (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ A a T₀ : ℝ, 0 < A ∧ 0 < a ∧ Real.exp 9 ≤ T₀ ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ (K : ℕ) (T : ℝ), T₀ ≤ T →
        P {ω | T * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (K : ℝ)) * lambdaN (ξ : ℝ) W P 0 <
          lenObs (ξ : ℝ) (phiMN W P 0 K) (rectAB 1 1) ω} ≤
          ENNReal.ofReal (A * Real.exp (-a * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  obtain ⟨pa, ca, Ca, Cna, cna, Cpa, cpa, hpa, hpaH, hca, hCa, hCna, hcna, hCpa, hcpa,
    hapr⟩ := laneB_apriori_unit_square_power_tails ξ Q hQ ζ hζ
  obtain ⟨c0, C0, hc0, hC0, hwin⟩ := laneB_whiteNoise_median_window ξ Q hQ ζ hζ
  set y₀ : ℝ := 2 * (Real.log 3 + |Real.log ca| + |Real.log c0| + |Real.log Ca|) + 9
    with hy₀
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h1 := abs_nonneg (Real.log ca)
  have h2 := abs_nonneg (Real.log c0)
  have h3 := abs_nonneg (Real.log Ca)
  have hy₀9 : 9 ≤ y₀ := by rw [hy₀]; linarith
  refine ⟨Cpa, cpa / 8, Real.exp y₀, hCpa, by positivity, Real.exp_le_exp.mpr hy₀9, ?_⟩
  intro Ω _ P W hW K T hT
  have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT
  set y : ℝ := Real.log T with hydef
  have hyy₀ : y₀ ≤ y := by rw [hydef, Real.le_log_iff_exp_le hTpos]; exact hT
  set T' : ℝ := c0 * T with hT'
  have hT'pos : 0 < T' := mul_pos hc0 hTpos
  have hlogT' : Real.log T' = Real.log c0 + y := by rw [hT', Real.log_mul hc0.ne' hTpos.ne']
  have hcaT : 3 < ca * T' := by
    rw [← Real.exp_log (mul_pos hca hT'pos), ← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    refine Real.exp_lt_exp.mpr ?_
    rw [Real.log_mul hca.ne' hT'pos.ne', hlogT']
    have := neg_abs_le (Real.log ca); have := neg_abs_le (Real.log c0); linarith
  have hTCa : 3 < T' / Ca := by
    rw [← Real.exp_log (div_pos hT'pos hCa), ← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    refine Real.exp_lt_exp.mpr ?_
    rw [Real.log_div hT'pos.ne' hCa.ne', hlogT']
    have := le_abs_self (Real.log Ca); have := neg_abs_le (Real.log c0); linarith
  have hlam : c0 ≤ lambdaN (ξ : ℝ) W P 0 := by
    have := (hwin P W hW 0).1; simpa using this
  have hsub : {ω | T * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (K : ℝ)) *
      lambdaN (ξ : ℝ) W P 0 < lenObs (ξ : ℝ) (phiMN W P 0 K) (rectAB 1 1) ω} ⊆
      {ω | T' * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (K : ℝ)) <
        lenObs (ξ : ℝ) (phiMN W P 0 K) (rectAB 1 1) ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    refine lt_of_le_of_lt ?_ hω
    have hg : 0 ≤ (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (K : ℝ)) := by positivity
    calc T' * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (K : ℝ))
        = T * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (K : ℝ)) * c0 := by rw [hT']; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlam (mul_nonneg hTpos.le hg)
  refine (measure_mono hsub).trans (((hapr P W hW K T' hcaT hTCa).2).trans ?_)
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCpa.le)
  set L' : ℝ := Real.log (T' / Ca) with hL'
  have hL'eq : L' = Real.log c0 + y - Real.log Ca := by
    rw [hL', Real.log_div hT'pos.ne' hCa.ne', hlogT']
  have hlo : y / 2 ≤ L' := by
    rw [hL'eq]; have := neg_abs_le (Real.log c0); have := le_abs_self (Real.log Ca); linarith
  have hhi : L' ≤ 2 * y := by
    rw [hL'eq]; have := le_abs_self (Real.log c0); have := neg_abs_le (Real.log Ca); linarith
  have hy9 : 9 ≤ y := hy₀9.trans hyy₀
  have hL'1 : 1 < L' := by linarith
  have hlL' : 0 < Real.log L' := Real.log_pos hL'1
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog2y : Real.log L' ≤ 2 * Real.log y := by
    calc Real.log L' ≤ Real.log (2 * y) := Real.log_le_log (by linarith) hhi
      _ = Real.log 2 + Real.log y := Real.log_mul (by norm_num) (by linarith)
      _ ≤ Real.log y + Real.log y := by
          have : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) (by linarith)
          linarith
      _ = 2 * Real.log y := by ring
  have hsq : (y / 2) ^ 2 ≤ L' ^ 2 := pow_le_pow_left₀ (by linarith) hlo 2
  
  have hnum : cpa / 8 * y ^ 2 * 2 ≤ cpa * L' ^ 2 := by nlinarith
  have hdiv : cpa / 8 * y ^ 2 / Real.log y ≤ cpa * L' ^ 2 / Real.log L' := by
    rw [div_le_div_iff₀ hly hlL']
    calc cpa / 8 * y ^ 2 * Real.log L' ≤ cpa / 8 * y ^ 2 * (2 * Real.log y) :=
          mul_le_mul_of_nonneg_left hlog2y (by positivity)
      _ = (cpa / 8 * y ^ 2 * 2) * Real.log y := by ring
      _ ≤ cpa * L' ^ 2 * Real.log y := mul_le_mul_of_nonneg_right hnum hly.le
  have e1 : -cpa * L' ^ 2 / Real.log L' = -(cpa * L' ^ 2 / Real.log L') := by ring
  have e2 : -(cpa / 8) * y ^ 2 / Real.log y = -(cpa / 8 * y ^ 2 / Real.log y) := by ring
  linarith

end SupercriticalLQGUniqueness.B2.DG20Conc
