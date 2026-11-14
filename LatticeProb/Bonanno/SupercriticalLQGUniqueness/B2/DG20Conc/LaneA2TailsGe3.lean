/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2TailsGe3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2TailAbsorb

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

 


theorem laneA2_repaired_rectangle_tails_ge3 {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p Aneg Apos Cneg cNeg Cpos cPos : ℝ,
      0 < p ∧ p < 2⁻¹ ∧ 1 ≤ Aneg ∧ 1 ≤ Apos ∧
      0 < Cneg ∧ 0 < cNeg ∧ 0 < Cpos ∧ 0 < cPos ∧
      LaneA2HasUnitTails.{u} ξ p ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (_hW : IsWhiteNoise P W)
        (m : ℕ) (_hm : 3 ≤ m) (B : ℝ) (_hB : 1 ≤ B)
        (_hΛ : LambdaN ξ W P m (ENNReal.ofReal p) ≤ B)
        (T : ℝ) (_hT : 36 < T) (v : Circle) (c : ℂ),
        P {ω | T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω) 3 v c 1 3 <
          (Aneg * B^4 * T)⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} ≤
          ENNReal.ofReal (Cneg * Real.exp (-cNeg * (Real.log T)^2)) ∧
        P {ω | Apos * T * LambdaN ξ W P m (ENNReal.ofReal p) *
            ellN ξ W P m (ENNReal.ofReal p) <
            T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω) 3 v c 3 1} ≤
          ENNReal.ofReal (Cpos * Real.exp
            (-cPos * (Real.log T)^2 / Real.log (Real.log T))) := by
  obtain ⟨p, Cn, cn, Cp, cp, Dr, Df, CL, AL, CU, AU,
    hp, hpHalf, hCn, hcn, hCp, hcp, hDr, hDf, hCL, hAL, hCU, hAU, hunit, hraw⟩ :=
      laneA2_repaired_raw_tails_ge3 hξ
  let cgL : ℝ := 3 / (4 * ξ^2 * AL^2 * Real.log 4)
  let cgU : ℝ := 3 / (4 * ξ^2 * AU^2 * Real.log 4)
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hloglog3 : 0 < Real.log (Real.log 3) := by
    apply Real.log_pos
    linarith [Real.log_three_gt_d9]
  have hcgL : 0 < cgL := by dsimp [cgL]; positivity
  have hcgU : 0 < cgU := by dsimp [cgU]; positivity
  refine ⟨p, 8 * Df^3, Dr, CL + Cn, min cgL (cn / 4),
    CU + Cp, min (cgU * Real.log (Real.log 3)) (cp / 16),
    hp, hpHalf, ?_, hDr, ?_, ?_, ?_, ?_,
    ⟨Cn, cn, Cp, cp, hCn, hcn, hCp, hcp, hunit⟩, ?_⟩
  · have : 1 ≤ Df^3 := one_le_pow₀ hDf
    nlinarith
  · linarith
  · exact lt_min hcgL (by positivity)
  · linarith
  · exact lt_min (mul_pos hcgU hloglog3) (by positivity)
  · intro Ω _ P W hW m hm B hB hΛ T hT v c
    obtain ⟨S, M, hS, hM, hSsq, hlogS, heUp, heLow, hlow, hup⟩ :=
      hraw P W hW m hm B hB hΛ T hT v c
    refine ⟨?_, ?_⟩
    · exact hlow.trans
        (laneA2_lower_tail_absorb hξ hAL hCL.le hCn.le heUp hlogS)
    · have h := hup.trans
        (laneA2_upper_tail_absorb hξ hAU hCU.le hCp.le hcp.le
          hS hSsq heUp hlogS)
      simpa only [cgU, mul_div_assoc] using h

end SupercriticalLQGUniqueness.B2.DG20Conc
