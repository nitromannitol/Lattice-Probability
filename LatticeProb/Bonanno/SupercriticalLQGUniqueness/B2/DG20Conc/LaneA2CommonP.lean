/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2CommonP at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2ForwardBridge

 






set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

theorem laneA2_common_p_unit_tails_and_bridges {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p Cneg cNeg Cpos cPos Drev Dfor : ℝ,
      0 < p ∧ p < 2⁻¹ ∧ 0 < Cneg ∧ 0 < cNeg ∧
      0 < Cpos ∧ 0 < cPos ∧ 1 ≤ Drev ∧ 1 ≤ Dfor ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (_hW : IsWhiteNoise P W),
        (∀ (m : ℕ) (T : ℝ), 3 < T →
          P {ω | lenObs ξ (phiMN W P 0 m) (rectAB 1 3) ω <
            T⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} ≤
            ENNReal.ofReal (Cneg * Real.exp (-cNeg * (Real.log T)^2))) ∧
        (∀ (m : ℕ) (T : ℝ), 3 < T →
          P {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
            ellN ξ W P m (ENNReal.ofReal p) <
            lenObs ξ (phiMN W P 0 m) (rectAB 3 1) ω} ≤
            ENNReal.ofReal (Cpos * Real.exp
              (-cPos * (Real.log T)^2 / Real.log (Real.log T)))) ∧
        (∀ (m : ℕ), 3 ≤ m →
          ellN ξ W P (m - 3) (ENNReal.ofReal p) ≤
            Drev * ellN ξ W P m (ENNReal.ofReal p)) ∧
        (∀ (m : ℕ), 3 ≤ m → ∀ (B : ℝ), 1 ≤ B →
          LambdaN ξ W P m (ENNReal.ofReal p) ≤ B →
          ellN ξ W P m (ENNReal.ofReal p) ≤
            Dfor ^ 3 * B ^ 4 * ellN ξ W P (m - 3) (ENNReal.ofReal p)) := by
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise
  let P₀ := LQGDimension.ExistAsm.stdP
  obtain ⟨pNeg, hpNeg, hNeg⟩ := dddf_cor17 (P := P₀) hW₀ hξ
  obtain ⟨pPos, hpPos, hPos⟩ := dddf_prop18 (P := P₀) hW₀ hξ
  obtain ⟨pRev, hpRev, hRev⟩ := laneA2_reverse_three_octave hξ
  obtain ⟨pFor, hpFor, hFor⟩ := laneA2_forward_three_octave hξ
  let p : ℝ := min pNeg (min pPos (min pRev (min pFor (1 / 4))))
  have hp : 0 < p := lt_min hpNeg
    (lt_min hpPos (lt_min hpRev (lt_min hpFor (by norm_num))))
  have hpNeg' : p ≤ pNeg := min_le_left _ _
  have hpPos' : p ≤ pPos := (min_le_right _ _).trans (min_le_left _ _)
  have hpRev' : p ≤ pRev :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hpFor' : p ≤ pFor :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hpHalf : p < 2⁻¹ := by
    have hquarter : p ≤ (1 / 4 : ℝ) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
    norm_num at hquarter ⊢
    linarith
  obtain ⟨Cneg, cNeg, hCneg, hcNeg, htailNeg⟩ := hNeg p hp hpNeg'
  obtain ⟨Cpos, cPos, hCpos, hcPos, htailPos⟩ := hPos p hp hpPos'
  obtain ⟨Drev, hDrev, hreverse⟩ := hRev p hp hpRev'
  obtain ⟨Dfor, hDfor, hforward⟩ := hFor p hp hpFor'
  let M : ℝ := (Real.log (Real.exp 2))^2 / Real.log (Real.log 3)
  let Cpos' : ℝ := Cpos + Real.exp (cPos * M)
  have hCpos' : 0 < Cpos' := by dsimp [Cpos']; positivity
  refine ⟨p, Cneg, cNeg, Cpos', cPos, Drev, Dfor, hp, hpHalf,
    hCneg, hcNeg, hCpos', hcPos, hDrev, hDfor, ?_⟩
  intro Ω _ P W hW
  have hrev : ∀ (m : ℕ), 3 ≤ m →
      ellN ξ W P (m - 3) (ENNReal.ofReal p) ≤
        Drev * ellN ξ W P m (ENNReal.ofReal p) :=
    hreverse P W hW
  refine ⟨?_, ?_, hrev, ?_⟩
  · intro m T hT
    have hT0 : 0 < T := by linarith
    have hs : 0 < Real.log T := Real.log_pos (by linarith)
    have he : Real.exp (-Real.log T) = T⁻¹ := by
      rw [Real.exp_neg, Real.exp_log hT0]
    have hcanon := htailNeg m (Real.log T) hs
    have hset : {ω | lenObs ξ (phiMN W P 0 m) (rectAB 1 3) ω <
        T⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} ⊆
        {ω | lenObs ξ (phiMN W P 0 m) (rectAB 1 3) ω ≤
          T⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} := by
      intro ω hω
      change lenObs ξ (phiMN W P 0 m) (rectAB 1 3) ω < _ at hω
      exact hω.le
    apply (measure_mono hset).trans
    rw [laneA_ellN_eq hW hW₀ ξ m (ENNReal.ofReal p)]
    have hprob := laneA_prob_lenObs_eq hW hW₀ ξ m (rectAB 1 3)
      (S := Set.Iic (T⁻¹ * ellN ξ W₀ P₀ m (ENNReal.ofReal p))) measurableSet_Iic
    change P {ω | lenObs ξ (phiMN W P 0 m) (rectAB 1 3) ω ≤ _} =
      P₀ {ω | lenObs ξ (phiMN W₀ P₀ 0 m) (rectAB 1 3) ω ≤ _} at hprob
    rw [hprob]
    simpa only [he, ellN] using hcanon
  · intro m T hT
    by_cases hbig : Real.exp 2 < T
    · have hT0 : 0 < T := (Real.exp_pos _).trans hbig
      have hs : 2 < Real.log T := by
        rw [← Real.log_exp (2 : ℝ)]
        exact Real.log_lt_log (Real.exp_pos _) hbig
      have hcanon := htailPos m (Real.log T) hs
      have hset : {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
          ellN ξ W P m (ENNReal.ofReal p) <
          lenObs ξ (phiMN W P 0 m) (rectAB 3 1) ω} ⊆
          {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
            ellN ξ W P m (ENNReal.ofReal p) ≤
            lenObs ξ (phiMN W P 0 m) (rectAB 3 1) ω} := by
        intro ω hω
        change _ < lenObs ξ (phiMN W P 0 m) (rectAB 3 1) ω at hω
        exact hω.le
      have hraw : P {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
          ellN ξ W P m (ENNReal.ofReal p) <
          lenObs ξ (phiMN W P 0 m) (rectAB 3 1) ω} ≤
          ENNReal.ofReal (Cpos * Real.exp
            (-cPos * (Real.log T)^2 / Real.log (Real.log T))) := by
        apply (measure_mono hset).trans
        rw [laneA_LambdaN_eq hW hW₀ ξ m (ENNReal.ofReal p),
          laneA_ellN_eq hW hW₀ ξ m (ENNReal.ofReal p)]
        have hprob := laneA_prob_lenObs_eq hW hW₀ ξ m (rectAB 3 1)
          (S := Set.Ici (T * LambdaN ξ W₀ P₀ m (ENNReal.ofReal p) *
            ellN ξ W₀ P₀ m (ENNReal.ofReal p))) measurableSet_Ici
        change P {ω | T * LambdaN ξ W₀ P₀ m (ENNReal.ofReal p) *
            ellN ξ W₀ P₀ m (ENNReal.ofReal p) ≤
            lenObs ξ (phiMN W P 0 m) (rectAB 3 1) ω} =
          P₀ {ω | T * LambdaN ξ W₀ P₀ m (ENNReal.ofReal p) *
            ellN ξ W₀ P₀ m (ENNReal.ofReal p) ≤
            lenObs ξ (phiMN W₀ P₀ 0 m) (rectAB 3 1) ω} at hprob
        rw [hprob]
        simpa only [Real.exp_log hT0] using hcanon
      apply hraw.trans
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right
        (by dsimp [Cpos']; linarith [Real.exp_pos (cPos * M)])
        (Real.exp_pos _).le
    · have hTup : T ≤ Real.exp 2 := le_of_not_gt hbig
      have : IsProbabilityMeasure P := hW.isProbabilityMeasure
      have hrate : (Real.log T)^2 / Real.log (Real.log T) ≤ M :=
        laneA_bounded_log_rate hT hTup
      have hprod : 0 ≤ cPos *
          (M - (Real.log T)^2 / Real.log (Real.log T)) := by
        exact mul_nonneg hcPos.le (sub_nonneg.mpr hrate)
      have hexp : 1 ≤ Real.exp (cPos * M) *
          Real.exp (-cPos * (Real.log T)^2 / Real.log (Real.log T)) := by
        rw [← Real.exp_add, ← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        convert hprod using 1; ring
      have hreal : 1 ≤ Cpos' * Real.exp
          (-cPos * (Real.log T)^2 / Real.log (Real.log T)) := by
        dsimp [Cpos']
        exact hexp.trans (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left hCpos.le) (Real.exp_pos _).le)
      calc
        P {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
            ellN ξ W P m (ENNReal.ofReal p) <
            lenObs ξ (phiMN W P 0 m) (rectAB 3 1) ω} ≤ 1 := prob_le_one
        _ = ENNReal.ofReal (1 : ℝ) := by norm_num
        _ ≤ ENNReal.ofReal (Cpos' * Real.exp
          (-cPos * (Real.log T)^2 / Real.log (Real.log T))) :=
            ENNReal.ofReal_le_ofReal hreal
  · intro m hm B hB hΛ
    exact hforward P W hW B hB m hm hΛ

end SupercriticalLQGUniqueness.B2.DG20Conc
