/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneATails at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneALaw
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.C17
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S2

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

variable {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂]
  {P : Measure Ω} {P₂ : Measure Ω₂}

 
theorem laneA_prob_lenObs_eq {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ}
    (hW : IsWhiteNoise P W) (hV : IsWhiteNoise P₂ V) (ξ : ℝ) (m : ℕ)
    (R : MarkedRect) {S : Set ℝ} (hS : MeasurableSet S) :
    P {ω | lenObs ξ (phiMN W P 0 m) R ω ∈ S} =
      P₂ {ω | lenObs ξ (phiMN V P₂ 0 m) R ω ∈ S} := by
  have hφW := isPhiVersion_phiMN hW (Nat.zero_le m)
  have hφV := isPhiVersion_phiMN hV (Nat.zero_le m)
  change P (lenObs ξ (phiMN W P 0 m) R ⁻¹' S) =
    P₂ (lenObs ξ (phiMN V P₂ 0 m) R ⁻¹' S)
  rw [← Measure.map_apply (measurable_lenObs hφW.cont hφW.meas R) hS,
    ← Measure.map_apply (measurable_lenObs hφV.cont hφV.meas R) hS,
    laneA_law_lenObs_eq hW hV ξ m R]

 



theorem laneA_unit_rectangle_tails_largeT {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p Cneg cNeg Cpos cPos : ℝ,
      0 < p ∧ p < 2⁻¹ ∧ 0 < Cneg ∧ 0 < cNeg ∧ 0 < Cpos ∧ 0 < cPos ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
        (∀ (m : ℕ) (T : ℝ), 3 < T →
          P {ω | lenObs ξ (phiMN W P 0 m) (rectAB 1 3) ω <
            T⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} ≤
            ENNReal.ofReal (Cneg * Real.exp (-cNeg * (Real.log T)^2))) ∧
        (∀ (m : ℕ) (T : ℝ), Real.exp 2 < T →
          P {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
            ellN ξ W P m (ENNReal.ofReal p) <
            lenObs ξ (phiMN W P 0 m) (rectAB 3 1) ω} ≤
            ENNReal.ofReal (Cpos * Real.exp
              (-cPos * (Real.log T)^2 / Real.log (Real.log T)))) := by
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise
  let P₀ := LQGDimension.ExistAsm.stdP
  obtain ⟨pNeg, hpNeg, hNeg⟩ := dddf_cor17 (P := P₀) hW₀ hξ
  obtain ⟨pPos, hpPos, hPos⟩ := dddf_prop18 (P := P₀) hW₀ hξ
  let p : ℝ := min pNeg (min pPos (1 / 4))
  have hp : 0 < p := lt_min hpNeg (lt_min hpPos (by norm_num))
  have hp₁ : p ≤ pNeg := min_le_left _ _
  have hp₂ : p ≤ pPos := (min_le_right _ _).trans (min_le_left _ _)
  have hpHalf : p < 2⁻¹ := by
    have hquarter : p ≤ (1 / 4 : ℝ) :=
      (min_le_right _ _).trans (min_le_right _ _)
    norm_num at hquarter ⊢
    linarith
  obtain ⟨Cneg, cNeg, hCneg, hcNeg, htailNeg⟩ := hNeg p hp hp₁
  obtain ⟨Cpos, cPos, hCpos, hcPos, htailPos⟩ := hPos p hp hp₂
  refine ⟨p, Cneg, cNeg, Cpos, cPos, hp, hpHalf, hCneg, hcNeg, hCpos, hcPos,
    fun P W hW => ?_⟩
  constructor
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
    have hT0 : 0 < T := (Real.exp_pos _).trans hT
    have hs : 2 < Real.log T := by
      rw [← Real.log_exp (2 : ℝ)]
      exact Real.log_lt_log (Real.exp_pos _) hT
    have he : Real.exp (Real.log T) = T := Real.exp_log hT0
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
    simpa only [he] using hcanon

 

private theorem laneA_log_ratio_bound {T : ℝ} (hT : 3 < T)
    (hTup : T ≤ Real.exp 2) :
    (Real.log T)^2 / Real.log (Real.log T) ≤
      4 / Real.log (Real.log 3) := by
  have hlog3 : 1 < Real.log 3 := by
    have h := Real.log_three_gt_d9
    linarith
  have hlogT : 1 < Real.log T :=
    hlog3.trans (Real.log_lt_log (by norm_num) hT)
  have hll3 : 0 < Real.log (Real.log 3) := Real.log_pos hlog3
  have hllT : 0 < Real.log (Real.log T) := Real.log_pos hlogT
  have hlogTle : Real.log T ≤ 2 := by
    simpa only [Real.log_exp] using Real.log_le_log (by linarith) hTup
  have hsq : (Real.log T)^2 ≤ 4 := by nlinarith
  have hllle : Real.log (Real.log 3) ≤ Real.log (Real.log T) :=
    Real.log_le_log (by linarith)
      (Real.log_le_log (by norm_num) hT.le)
  exact (div_le_div_of_nonneg_right hsq hllT.le).trans
    (div_le_div_of_nonneg_left (by norm_num) hll3 hllle)

 

theorem laneA_unit_rectangle_tails {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p Cneg cNeg Cpos cPos : ℝ,
      0 < p ∧ p < 2⁻¹ ∧ 0 < Cneg ∧ 0 < cNeg ∧ 0 < Cpos ∧ 0 < cPos ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
        (∀ (m : ℕ) (T : ℝ), 3 < T →
          P {ω | lenObs ξ (phiMN W P 0 m) (rectAB 1 3) ω <
            T⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} ≤
            ENNReal.ofReal (Cneg * Real.exp (-cNeg * (Real.log T)^2))) ∧
        (∀ (m : ℕ) (T : ℝ), 3 < T →
          P {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
            ellN ξ W P m (ENNReal.ofReal p) <
            lenObs ξ (phiMN W P 0 m) (rectAB 3 1) ω} ≤
            ENNReal.ofReal (Cpos * Real.exp
              (-cPos * (Real.log T)^2 / Real.log (Real.log T)))) := by
  obtain ⟨p, Cneg, cNeg, Cpos, cPos, hp, hpHalf, hCneg, hcNeg,
    hCpos, hcPos, htail⟩ := laneA_unit_rectangle_tails_largeT hξ
  have hlog3 : 1 < Real.log 3 := by
    have h := Real.log_three_gt_d9
    linarith
  have hll3 : 0 < Real.log (Real.log 3) := Real.log_pos hlog3
  let M : ℝ := 4 / Real.log (Real.log 3)
  let Cpos' : ℝ := Cpos + Real.exp (cPos * M)
  have hCpos' : 0 < Cpos' := by dsimp [Cpos']; positivity
  refine ⟨p, Cneg, cNeg, Cpos', cPos, hp, hpHalf, hCneg, hcNeg,
    hCpos', hcPos, fun P W hW => ?_⟩
  obtain ⟨hlow, hupp⟩ := htail P W hW
  constructor
  · exact hlow
  · intro m T hT
    by_cases hbig : Real.exp 2 < T
    · have h := hupp m T hbig
      apply h.trans
      apply ENNReal.ofReal_le_ofReal
      dsimp [Cpos']
      have he : 0 ≤ Real.exp (-cPos * (Real.log T)^2 /
          Real.log (Real.log T)) := (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (Real.exp_pos _).le) he
    · have hTup : T ≤ Real.exp 2 := le_of_not_gt hbig
      have : IsProbabilityMeasure P := hW.isProbabilityMeasure
      have hq := laneA_log_ratio_bound hT hTup
      have hq' : (Real.log T)^2 / Real.log (Real.log T) ≤ M := hq
      have hprod : 0 ≤ cPos * (M -
          (Real.log T)^2 / Real.log (Real.log T)) := by
        exact mul_nonneg hcPos.le (sub_nonneg.mpr hq')
      have hexp : 1 ≤ Real.exp (cPos * M) *
          Real.exp (-cPos * (Real.log T)^2 /
            Real.log (Real.log T)) := by
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

end SupercriticalLQGUniqueness.B2.DG20Conc
