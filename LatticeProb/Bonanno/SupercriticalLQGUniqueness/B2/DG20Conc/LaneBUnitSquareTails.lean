/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBUnitSquareTails at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBAprioriWindow
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneATails
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BTight

 






set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

 

theorem laneB_unit_square_tails {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p Cneg cNeg Cpos cPos : ℝ,
      0 < p ∧ p < 2⁻¹ ∧ 0 < Cneg ∧ 0 < cNeg ∧ 0 < Cpos ∧ 0 < cPos ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
        (∀ (m : ℕ) (T : ℝ), 3 < T →
          P {ω | lenObs ξ (phiMN W P 0 m) (rectAB 1 1) ω <
            T⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} ≤
            ENNReal.ofReal (Cneg * Real.exp (-cNeg * (Real.log T)^2))) ∧
        (∀ (m : ℕ) (T : ℝ), 3 < T →
          P {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
            ellN ξ W P m (ENNReal.ofReal p) <
            lenObs ξ (phiMN W P 0 m) (rectAB 1 1) ω} ≤
            ENNReal.ofReal (Cpos * Real.exp
              (-cPos * (Real.log T)^2 / Real.log (Real.log T)))) := by
  obtain ⟨p, Cneg, cNeg, Cpos, cPos, hp, hpHalf, hCn, hcn, hCp, hcp,
    htails⟩ := laneA_unit_rectangle_tails hξ
  refine ⟨p, Cneg, cNeg, Cpos, cPos, hp, hpHalf, hCn, hcn, hCp, hcp, ?_⟩
  intro Ω _ P W hW
  obtain ⟨hneg, hpos⟩ := htails P W hW
  constructor
  · intro m T hT
    calc
      P {ω | lenObs ξ (phiMN W P 0 m) (rectAB 1 1) ω <
          T⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} ≤
        P {ω | lenObs ξ (phiMN W P 0 m) (rectAB 1 3) ω <
          T⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} := by
          apply measure_mono
          intro ω hω
          exact lt_of_le_of_lt (T20B.lenObs_13_le_11
            (isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω) hω
      _ ≤ _ := hneg m T hT
  · intro m T hT
    calc
      P {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
          ellN ξ W P m (ENNReal.ofReal p) <
          lenObs ξ (phiMN W P 0 m) (rectAB 1 1) ω} ≤
        P {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
          ellN ξ W P m (ENNReal.ofReal p) <
          lenObs ξ (phiMN W P 0 m) (rectAB 3 1) ω} := by
          apply measure_mono
          intro ω hω
          exact lt_of_lt_of_le hω (T20B.lenObs_11_le_31
            (isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)
      _ ≤ _ := hpos m T hT

 



theorem laneB_apriori_unit_square_power_tails
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ p c C Cneg cNeg Cpos cPos : ℝ,
      0 < p ∧ p < 2⁻¹ ∧ 0 < c ∧ 0 < C ∧
      0 < Cneg ∧ 0 < cNeg ∧ 0 < Cpos ∧ 0 < cPos ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
        ∀ (m : ℕ) (T : ℝ), 3 < c * T → 3 < T / C →
          P {ω | lenObs (ξ : ℝ) (phiMN W P 0 m) (rectAB 1 1) ω <
            T⁻¹ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (m : ℝ))} ≤
            ENNReal.ofReal (Cneg * Real.exp (-cNeg * (Real.log (c * T))^2)) ∧
          P {ω | T * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (m : ℝ)) <
            lenObs (ξ : ℝ) (phiMN W P 0 m) (rectAB 1 1) ω} ≤
            ENNReal.ofReal (Cpos * Real.exp
              (-cPos * (Real.log (T / C))^2 / Real.log (Real.log (T / C)))) := by
  obtain ⟨p, Cneg, cNeg, Cpos, cPos, hp, hpHalf, hCn, hcn, hCp, hcp,
    htails⟩ := laneB_unit_square_tails ξ.property
  obtain ⟨c, C, hc, hC, hwindow⟩ :=
    laneB_apriori_unit_quantile_window ξ Q hQ p ζ hp hpHalf hζ
  refine ⟨p, c, C, Cneg, cNeg, Cpos, cPos, hp, hpHalf, hc, hC,
    hCn, hcn, hCp, hcp, ?_⟩
  intro Ω _ P W hW m T hTlo hThi
  have hT : 0 < T := by
    have : 0 < c * T := lt_trans (by norm_num : (0 : ℝ) < 3) hTlo
    rw [mul_comm] at this
    exact pos_of_mul_pos_left this hc.le
  obtain ⟨hql, -, hqu⟩ := hwindow P W hW m
  obtain ⟨hneg, hpos⟩ := htails P W hW
  have hscaleLower :
      T⁻¹ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (m : ℝ)) ≤
      (c * T)⁻¹ * ellN (ξ : ℝ) W P m (ENNReal.ofReal p) := by
    calc
      _ = (c * T)⁻¹ *
          (c * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (m : ℝ))) := by
            field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hql (inv_nonneg.mpr (mul_pos hc hT).le)
  have hscaleUpper :
      (T / C) * (LambdaN (ξ : ℝ) W P m (ENNReal.ofReal p) *
        ellN (ξ : ℝ) W P m (ENNReal.ofReal p)) ≤
      T * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (m : ℝ)) := by
    calc
      _ ≤ (T / C) *
          (C * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (m : ℝ))) :=
            mul_le_mul_of_nonneg_left hqu (div_nonneg hT.le hC.le)
      _ = _ := by field_simp
  constructor
  · calc
      P {ω | lenObs (ξ : ℝ) (phiMN W P 0 m) (rectAB 1 1) ω <
          T⁻¹ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (m : ℝ))} ≤
        P {ω | lenObs (ξ : ℝ) (phiMN W P 0 m) (rectAB 1 1) ω <
          (c * T)⁻¹ * ellN (ξ : ℝ) W P m (ENNReal.ofReal p)} := by
            apply measure_mono
            intro ω hω
            exact lt_of_lt_of_le hω hscaleLower
      _ ≤ _ := hneg m (c * T) hTlo
  · calc
      P {ω | T * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (m : ℝ)) <
          lenObs (ξ : ℝ) (phiMN W P 0 m) (rectAB 1 1) ω} ≤
        P {ω | (T / C) * LambdaN (ξ : ℝ) W P m (ENNReal.ofReal p) *
          ellN (ξ : ℝ) W P m (ENNReal.ofReal p) <
          lenObs (ξ : ℝ) (phiMN W P 0 m) (rectAB 1 1) ω} := by
            apply measure_mono
            intro ω hω
            change (T / C) * LambdaN (ξ : ℝ) W P m (ENNReal.ofReal p) *
              ellN (ξ : ℝ) W P m (ENNReal.ofReal p) <
              lenObs (ξ : ℝ) (phiMN W P 0 m) (rectAB 1 1) ω
            simpa only [mul_assoc] using (lt_of_le_of_lt hscaleUpper hω)
      _ ≤ _ := hpos m (T / C) hThi

end SupercriticalLQGUniqueness.B2.DG20Conc
