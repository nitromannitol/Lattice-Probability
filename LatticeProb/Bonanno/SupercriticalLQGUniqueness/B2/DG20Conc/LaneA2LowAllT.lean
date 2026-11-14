/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2LowAllT at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2LowLargeT
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2BoundedT

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

private theorem bounded_event {Ω : Type*} [MeasurableSpace Ω]
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

theorem laneA2_low_tails_allT {ξ p : ℝ} (hξ : 0 < ξ)
    (hp : 0 < p) (hpHalf : p < 2⁻¹) :
    ∃ Cneg cNeg Cpos cPos : ℝ,
      0 < Cneg ∧ 0 < cNeg ∧ 0 < Cpos ∧ 0 < cPos ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (m : ℕ) (hm : m ≤ 2) (B : ℝ) (hB : 1 ≤ B)
        (T : ℝ) (hT : 3 < T) (v : Circle) (z : ℂ),
        P {ω | T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω) 3 v z 1 3 <
          (B^4 * T)⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} ≤
          ENNReal.ofReal (Cneg * Real.exp (-cNeg * (Real.log T)^2)) ∧
        P {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
            ellN ξ W P m (ENNReal.ofReal p) <
            T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω) 3 v z 3 1} ≤
          ENNReal.ofReal (Cpos * Real.exp
            (-cPos * (Real.log T)^2 / Real.log (Real.log T))) := by
  obtain ⟨H, C, c, hH, hC, hc, ht⟩ := laneA2_low_tails_largeT hξ hp hpHalf
  let Mn : ℝ := (Real.log H)^2
  let Mp : ℝ := (Real.log H)^2 / Real.log (Real.log 3)
  let cp : ℝ := c * Real.log (Real.log 3)
  have hcp : 0 < cp := by
    dsimp [cp]
    have hlog3 : 1 < Real.log 3 := by linarith [Real.log_three_gt_d9]
    exact mul_pos hc (Real.log_pos hlog3)
  refine ⟨C + Real.exp (c * Mn), c, C + Real.exp (cp * Mp), cp,
    by positivity, hc, by positivity, hcp, ?_⟩
  intro Ω _ P W hW m hm B hB T hT v z
  haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  by_cases hbig : H < T
  · obtain ⟨hl, hu⟩ := ht P W hW m hm B hB T hbig v z
    constructor
    · exact hl.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right
          (show C ≤ C + Real.exp (c * Mn) from
            le_add_of_nonneg_right (Real.exp_pos _).le)
          (Real.exp_pos _).le))
    · exact hu.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right
          (show C ≤ C + Real.exp (cp * Mp) from
            le_add_of_nonneg_right (Real.exp_pos _).le)
          (Real.exp_pos _).le))
  · have hTle : T ≤ H := le_of_not_gt hbig
    have hlog : 0 ≤ Real.log T := (Real.log_pos (by linarith : 1 < T)).le
    have hlogle : Real.log T ≤ Real.log H :=
      Real.log_le_log (by linarith) hTle
    have hnrate : (Real.log T)^2 ≤ Mn := by dsimp [Mn]; nlinarith
    have hprate : (Real.log T)^2 / Real.log (Real.log T) ≤ Mp :=
      laneA_bounded_log_rate hT hTle
    constructor
    · apply (bounded_event P _ hc hnrate).trans
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right
        (show Real.exp (c * Mn) ≤ C + Real.exp (c * Mn) from
          le_add_of_nonneg_left hC.le) (Real.exp_pos _).le
    · have hh := (bounded_event P
        {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
          ellN ξ W P m (ENNReal.ofReal p) <
          T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω) 3 v z 3 1}
        hcp hprate).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
          (show Real.exp (cp * Mp) ≤ C + Real.exp (cp * Mp) from
            le_add_of_nonneg_left hC.le) (Real.exp_pos _).le))
      simpa only [mul_div_assoc] using hh

end SupercriticalLQGUniqueness.B2.DG20Conc
