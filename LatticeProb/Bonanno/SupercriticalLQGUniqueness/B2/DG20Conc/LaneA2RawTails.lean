/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2RawTails at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Rate
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2CommonP
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2UnitTails

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

 


theorem laneA2_repaired_raw_tails_ge3 {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p Cneg cNeg Cpos cPos Drev Dfor CL AL CU AU : ℝ,
      0 < p ∧ p < 2⁻¹ ∧ 0 < Cneg ∧ 0 < cNeg ∧
      0 < Cpos ∧ 0 < cPos ∧ 1 ≤ Drev ∧ 1 ≤ Dfor ∧
      0 < CL ∧ 0 < AL ∧ 0 < CU ∧ 0 < AU ∧
      LaneA2UnitTails.{u} ξ p Cneg cNeg Cpos cPos ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (_hW : IsWhiteNoise P W)
        (m : ℕ) (_hm : 3 ≤ m) (B : ℝ) (_hB : 1 ≤ B)
        (_hΛ : LambdaN ξ W P m (ENNReal.ofReal p) ≤ B)
        (T : ℝ) (_hT : 36 < T) (v : Circle) (c : ℂ),
        ∃ S M : ℝ, 6 < S ∧ 0 < M ∧ S ^ 2 = T ∧
          Real.log S = Real.log T / 2 ∧
          Real.exp (|ξ| * M) = S ∧
          Real.exp (-(|ξ| * M)) = S⁻¹ ∧
          P {ω | T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω) 3 v c 1 3 <
            (8 * Dfor ^ 3 * B ^ 4 * T)⁻¹ *
              ellN ξ W P m (ENNReal.ofReal p)} ≤
            ENNReal.ofReal (CL * Real.exp (-((M / AL)^2 * 3 / Real.log 4))) +
            ENNReal.ofReal (Cneg * Real.exp (-cNeg * (Real.log S)^2)) ∧
          P {ω | Drev * T * LambdaN ξ W P m (ENNReal.ofReal p) *
              ellN ξ W P m (ENNReal.ofReal p) <
              T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω) 3 v c 3 1} ≤
            ENNReal.ofReal (CU * Real.exp (-((M / AU)^2 * 3 / Real.log 4))) +
            ENNReal.ofReal (Cpos * Real.exp
              (-cPos * (Real.log (S / 2))^2 /
                Real.log (Real.log (S / 2)))) := by
  obtain ⟨p, Cneg, cNeg, Cpos, cPos, Drev, Dfor,
    hp, hpHalf, hCneg, hcNeg, hCpos, hcPos, hDrev, hDfor, hcommon⟩ :=
      laneA2_common_p_unit_tails_and_bridges hξ
  have htailNeg : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
      (m : ℕ) (T : ℝ), 3 < T →
      P {ω | lenObs ξ (phiMN W P 0 m) (rectAB 1 3) ω <
        T⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} ≤
        ENNReal.ofReal (Cneg * Real.exp (-cNeg * (Real.log T)^2)) := by
    intro Ω _ P W hW m T hT
    exact (hcommon P W hW).1 m T hT
  have htailPos : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
      (m : ℕ) (T : ℝ), 3 < T →
      P {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
        ellN ξ W P m (ENNReal.ofReal p) <
        lenObs ξ (phiMN W P 0 m) (rectAB 3 1) ω} ≤
        ENNReal.ofReal (Cpos * Real.exp
          (-cPos * (Real.log T)^2 / Real.log (Real.log T))) := by
    intro Ω _ P W hW m T hT
    exact (hcommon P W hW).2.1 m T hT
  obtain ⟨CL, AL, hCL, hAL, hlow⟩ :=
    laneA2_canonical_lower_of_unit_tail (ξ := ξ) (p := p) htailNeg
  obtain ⟨CU, AU, hCU, hAU, hup⟩ :=
    laneA2_canonical_upper_of_unit_tail (ξ := ξ) (p := p)
      hp (by norm_num at hpHalf ⊢; exact hpHalf.le) htailPos
  have hunit : LaneA2UnitTails.{u} ξ p Cneg cNeg Cpos cPos := by
    intro Ω _ P W hW m T hT
    exact ⟨htailNeg P W hW m T hT, htailPos P W hW m T hT⟩
  refine ⟨p, Cneg, cNeg, Cpos, cPos, Drev, Dfor, CL, AL, CU, AU,
    hp, hpHalf, hCneg, hcNeg, hCpos, hcPos, hDrev, hDfor,
    hCL, hAL, hCU, hAU, hunit, ?_⟩
  intro Ω _ P W hW m hm B hB hΛ T hT v c
  obtain ⟨S, M, hS, hM, hSsq, hlogS, heUp, heLow⟩ :=
    laneA2_split_parameter hξ hT
  refine ⟨S, M, hS, hM, hSsq, hlogS, heUp, heLow, ?_, ?_⟩
  · have hfor := (hcommon P W hW).2.2.2 m hm B hB hΛ
    have hth : (8 * Dfor ^ 3 * B ^ 4 * T)⁻¹ *
        ellN ξ W P m (ENNReal.ofReal p) ≤
        Real.exp (-(|ξ| * M)) *
          ((1 / 8) * S⁻¹ * ellN ξ W P (m - 3) (ENNReal.ofReal p)) := by
      rw [heLow]
      exact laneA2_lower_bridge_threshold (by linarith : 0 < Dfor)
        (by linarith : 0 < B) (by linarith : 0 < S) hSsq hfor
    have hlaw := laneA2_mrectLen_law_three (ξ := ξ) hW m v c 1 3
      (S := Set.Iio ((8 * Dfor ^ 3 * B ^ 4 * T)⁻¹ *
        ellN ξ W P m (ENNReal.ofReal p))) measurableSet_Iio
    simp only [mul_one] at hlaw
    have he : (1 / 8 : ℝ) * (3 : ℝ) = 3 / 8 := by norm_num
    rw [he] at hlaw
    change P {ω | T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω)
      3 v c 1 3 ∈ Set.Iio ((8 * Dfor ^ 3 * B ^ 4 * T)⁻¹ *
        ellN ξ W P m (ENNReal.ofReal p))} ≤ _
    rw [hlaw]
    exact (measure_mono (fun ω hω => lt_of_lt_of_le hω hth)).trans
      (hlow P W hW m hm M hM S (by linarith))
  · have : IsProbabilityMeasure P := hW.isProbabilityMeasure
    have hrev := (hcommon P W hW).2.2.1 m hm
    have hΛmono : LambdaN ξ W P (m - 3) (ENNReal.ofReal p) ≤
        LambdaN ξ W P m (ENNReal.ofReal p) :=
      laneA2_LambdaN_mono P W ξ (ENNReal.ofReal p) (Nat.sub_le m 3)
    have hpq0 : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.mpr hp
    have hpq : ENNReal.ofReal p ≤ (2⁻¹ : ℝ≥0∞) := by
      have e : ENNReal.ofReal (1 / 2 : ℝ) = (2⁻¹ : ℝ≥0∞) := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
          ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num
      rw [← e]
      exact ENNReal.ofReal_le_ofReal (by norm_num at hpHalf ⊢; exact hpHalf.le)
    have hΛnow : 0 ≤ LambdaN ξ W P m (ENNReal.ofReal p) :=
      (T20B.LambdaN_pos (ξ := ξ) hW hpq0 hpq m).le
    have hℓprev : 0 ≤ ellN ξ W P (m - 3) (ENNReal.ofReal p) :=
      (T20B.ellN_pos (ξ := ξ) hW hpq0
        (lt_of_le_of_lt hpq (by norm_num)) (m - 3)).le
    have hℓnow : 0 ≤ ellN ξ W P m (ENNReal.ofReal p) :=
      (T20B.ellN_pos (ξ := ξ) hW hpq0
        (lt_of_le_of_lt hpq (by norm_num)) m).le
    have hth : Real.exp (|ξ| * M) *
        ((1 / 8) * S * LambdaN ξ W P (m - 3) (ENNReal.ofReal p) *
          ellN ξ W P (m - 3) (ENNReal.ofReal p)) ≤
        Drev * T * LambdaN ξ W P m (ENNReal.ofReal p) *
          ellN ξ W P m (ENNReal.ofReal p) := by
      rw [heUp]
      exact laneA2_upper_bridge_threshold (by linarith : 0 ≤ Drev)
        (by linarith : 0 < S)
        hSsq hΛmono hΛnow hℓprev hℓnow hrev
    have hlaw := laneA2_mrectLen_law_three (ξ := ξ) hW m v c 3 1
      (S := Set.Ioi (Drev * T * LambdaN ξ W P m (ENNReal.ofReal p) *
        ellN ξ W P m (ENNReal.ofReal p))) measurableSet_Ioi
    simp only [mul_one] at hlaw
    have he : (1 / 8 : ℝ) * (3 : ℝ) = 3 / 8 := by norm_num
    rw [he] at hlaw
    change P {ω | T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω)
      3 v c 3 1 ∈ Set.Ioi (Drev * T * LambdaN ξ W P m (ENNReal.ofReal p) *
        ellN ξ W P m (ENNReal.ofReal p))} ≤ _
    rw [hlaw]
    exact (measure_mono (fun ω hω => (hth.trans_lt hω).le)).trans
      (hup P W hW m hm M hM S hS)

end SupercriticalLQGUniqueness.B2.DG20Conc
