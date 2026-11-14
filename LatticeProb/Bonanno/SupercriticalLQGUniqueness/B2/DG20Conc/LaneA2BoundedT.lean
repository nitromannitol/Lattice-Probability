/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2BoundedT at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2TailsGe3
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneAShift

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

private theorem bounded_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : Set Ω)
    {c M r : ℝ} (hc : 0 < c) (hr : r ≤ M) :
    P E ≤ ENNReal.ofReal (Real.exp (c * M) * Real.exp (-c * r)) := by
  have he : 1 ≤ Real.exp (c * M) * Real.exp (-c * r) := by
    rw [← Real.exp_add, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    P E ≤ 1 := prob_le_one
    _ = ENNReal.ofReal (1 : ℝ) := by norm_num
    _ ≤ _ := ENNReal.ofReal_le_ofReal he

 
theorem laneA2_repaired_rectangle_tails_ge3_allT {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p Aneg Apos Cneg cNeg Cpos cPos : ℝ,
      0 < p ∧ p < 2⁻¹ ∧ 1 ≤ Aneg ∧ 1 ≤ Apos ∧
      0 < Cneg ∧ 0 < cNeg ∧ 0 < Cpos ∧ 0 < cPos ∧
      LaneA2HasUnitTails.{u} ξ p ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (_hW : IsWhiteNoise P W)
        (m : ℕ) (_hm : 3 ≤ m) (B : ℝ) (_hB : 1 ≤ B)
        (_hΛ : LambdaN ξ W P m (ENNReal.ofReal p) ≤ B)
        (T : ℝ) (_hT : 3 < T) (v : Circle) (c : ℂ),
        P {ω | T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω) 3 v c 1 3 <
          (Aneg * B^4 * T)⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} ≤
          ENNReal.ofReal (Cneg * Real.exp (-cNeg * (Real.log T)^2)) ∧
        P {ω | Apos * T * LambdaN ξ W P m (ENNReal.ofReal p) *
            ellN ξ W P m (ENNReal.ofReal p) <
            T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω) 3 v c 3 1} ≤
          ENNReal.ofReal (Cpos * Real.exp
            (-cPos * (Real.log T)^2 / Real.log (Real.log T))) := by
  obtain ⟨p, Aneg, Apos, Cneg, cNeg, Cpos, cPos,
    hp, hpHalf, hAn, hAp, hCn, hcn, hCp, hcp, hunit, ht⟩ :=
      laneA2_repaired_rectangle_tails_ge3 hξ
  let Mn : ℝ := (Real.log 36)^2
  let Mp : ℝ := (Real.log 36)^2 / Real.log (Real.log 3)
  refine ⟨p, Aneg, Apos, Cneg + Real.exp (cNeg * Mn), cNeg,
    Cpos + Real.exp (cPos * Mp), cPos, hp, hpHalf, hAn, hAp,
    by positivity, hcn, by positivity, hcp, hunit, ?_⟩
  intro Ω _ P W hW m hm B hB hΛ T hT v c
  have : IsProbabilityMeasure P := hW.isProbabilityMeasure
  by_cases hbig : 36 < T
  · obtain ⟨hn, hp'⟩ := ht P W hW m hm B hB hΛ T hbig v c
    constructor
    · exact hn.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right
          (by linarith [Real.exp_pos (cNeg * Mn)]) (Real.exp_pos _).le))
    · exact hp'.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right
          (by linarith [Real.exp_pos (cPos * Mp)]) (Real.exp_pos _).le))
  · have hTle : T ≤ 36 := le_of_not_gt hbig
    have hlog : 0 ≤ Real.log T := (Real.log_pos (by linarith : 1 < T)).le
    have hlogle : Real.log T ≤ Real.log 36 :=
      Real.log_le_log (by linarith) hTle
    have hnrate : (Real.log T)^2 ≤ Mn := by dsimp [Mn]; nlinarith
    have hprate : (Real.log T)^2 / Real.log (Real.log T) ≤ Mp :=
      laneA_bounded_log_rate hT hTle
    constructor
    · apply (bounded_probability P _ hcn hnrate).trans
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right
        (by linarith [Real.exp_pos (cNeg * Mn)]) (Real.exp_pos _).le
    · have hh := (bounded_probability P
        {ω | Apos * T * LambdaN ξ W P m (ENNReal.ofReal p) *
          ellN ξ W P m (ENNReal.ofReal p) <
          T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω) 3 v c 3 1}
        hcp hprate).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
          (show Real.exp (cPos * Mp) ≤ Cpos + Real.exp (cPos * Mp) from
            le_add_of_nonneg_left hCp.le) (Real.exp_pos _).le))
      simpa only [mul_div_assoc] using hh

end SupercriticalLQGUniqueness.B2.DG20Conc
