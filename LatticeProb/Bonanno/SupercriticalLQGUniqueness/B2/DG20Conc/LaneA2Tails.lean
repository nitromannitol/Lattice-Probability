/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Tails at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2LowAllT

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

private theorem tail_const_mono {C C' c c' r : ℝ}
    (hC : 0 ≤ C) (hCC : C ≤ C') (hcc : c' ≤ c) (hr : 0 ≤ r) :
    ENNReal.ofReal (C * Real.exp (-c * r)) ≤
      ENNReal.ofReal (C' * Real.exp (-c' * r)) := by
  apply ENNReal.ofReal_le_ofReal
  calc
    C * Real.exp (-c * r) ≤ C * Real.exp (-c' * r) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC
    _ ≤ C' * Real.exp (-c' * r) :=
      mul_le_mul_of_nonneg_right hCC (Real.exp_pos _).le

theorem laneA2_repaired_rectangle_tails {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p Aneg Apos Cneg cNeg Cpos cPos : ℝ,
      0 < p ∧ p < 2⁻¹ ∧ 1 ≤ Aneg ∧ 1 ≤ Apos ∧
      0 < Cneg ∧ 0 < cNeg ∧ 0 < Cpos ∧ 0 < cPos ∧
      LaneA2HasUnitTails.{u} ξ p ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (m : ℕ) (B : ℝ) (hB : 1 ≤ B)
        (hΛ : LambdaN ξ W P m (ENNReal.ofReal p) ≤ B)
        (T : ℝ) (hT : 3 < T) (v : Circle) (z : ℂ),
        P {ω | T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω) 3 v z 1 3 <
          (Aneg * B^4 * T)⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} ≤
          ENNReal.ofReal (Cneg * Real.exp (-cNeg * (Real.log T)^2)) ∧
        P {ω | Apos * T * LambdaN ξ W P m (ENNReal.ofReal p) *
            ellN ξ W P m (ENNReal.ofReal p) <
            T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω) 3 v z 3 1} ≤
          ENNReal.ofReal (Cpos * Real.exp
            (-cPos * (Real.log T)^2 / Real.log (Real.log T))) := by
  obtain ⟨p, Aneg, Apos, Cn, cn, Cp, cp,
    hp, hpHalf, hAn, hAp, hCn, hcn, hCp, hcp, hunit, hhigh⟩ :=
      laneA2_repaired_rectangle_tails_ge3_allT hξ
  obtain ⟨Ln, ln, Lp, lp, hLn, hln, hLp, hlp, hlow⟩ :=
    laneA2_low_tails_allT hξ hp hpHalf
  refine ⟨p, Aneg, Apos, Cn + Ln, min cn ln,
    Cp + Lp, min cp lp, hp, hpHalf, hAn, hAp,
    by linarith, lt_min hcn hln, by linarith, lt_min hcp hlp,
    hunit, ?_⟩
  intro Ω _ P W hW m B hB hΛ T hT v z
  haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hrate : 0 ≤ (Real.log T)^2 / Real.log (Real.log T) := by
    have hl3 : 1 < Real.log 3 := by linarith [Real.log_three_gt_d9]
    exact div_nonneg (sq_nonneg _) (Real.log_pos
      (hl3.trans (Real.log_lt_log (by norm_num) hT))).le
  by_cases hm : 3 ≤ m
  · obtain ⟨hn, hp'⟩ := hhigh P W hW m hm B hB hΛ T hT v z
    constructor
    · exact hn.trans (tail_const_mono hCn.le (by linarith)
        (min_le_left _ _) (sq_nonneg _))
    · exact hp'.trans (by
        simpa only [mul_div_assoc] using
          (tail_const_mono hCp.le (by linarith) (min_le_left _ _) hrate))
  · have hm2 : m ≤ 2 := by omega
    obtain ⟨hn, hp'⟩ := hlow P W hW m hm2 B hB T hT v z
    have hT0 : 0 < T := by linarith
    have hB4 : 1 ≤ B^4 := one_le_pow₀ hB
    have hden0 : 0 < B^4 * T := mul_pos (by linarith) hT0
    have hden : B^4 * T ≤ Aneg * (B^4 * T) := by nlinarith
    have hell0 : 0 ≤ ellN ξ W P m (ENNReal.ofReal p) := by
      have hpq0 : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.mpr hp
      have hpq1 : ENNReal.ofReal p < (1 : ℝ≥0∞) := by
        rw [ENNReal.ofReal_lt_one]
        norm_num at hpHalf ⊢
        linarith
      exact (T20B.ellN_pos hW hpq0 hpq1 m).le
    have hthn : (Aneg * B^4 * T)⁻¹ *
        ellN ξ W P m (ENNReal.ofReal p) ≤
        (B^4 * T)⁻¹ * ellN ξ W P m (ENNReal.ofReal p) := by
      have hi : (Aneg * (B^4 * T))⁻¹ ≤ (B^4 * T)⁻¹ :=
        (inv_le_inv₀ (mul_pos (by linarith) hden0) hden0).2 hden
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right hi hell0
    have hratio0 : 0 ≤ LambdaN ξ W P m (ENNReal.ofReal p) :=
      (T20B.LambdaN_pos hW (ENNReal.ofReal_pos.mpr hp)
        (by
          rw [← show ENNReal.ofReal (1/2 : ℝ) = (2⁻¹ : ℝ≥0∞) by
            rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
              ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num]
          exact ENNReal.ofReal_le_ofReal (by norm_num at hpHalf ⊢; exact hpHalf.le)) m).le
    have hbase : 0 ≤ T * LambdaN ξ W P m (ENNReal.ofReal p) *
        ellN ξ W P m (ENNReal.ofReal p) := by positivity
    have hthp : T * LambdaN ξ W P m (ENNReal.ofReal p) *
        ellN ξ W P m (ENNReal.ofReal p) ≤
        Apos * T * LambdaN ξ W P m (ENNReal.ofReal p) *
          ellN ξ W P m (ENNReal.ofReal p) := by
      nlinarith [mul_le_mul_of_nonneg_right hAp hbase]
    constructor
    · have hs : {ω | T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω)
          3 v z 1 3 < (Aneg * B^4 * T)⁻¹ *
            ellN ξ W P m (ENNReal.ofReal p)} ⊆
        {ω | T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω)
          3 v z 1 3 < (B^4 * T)⁻¹ *
            ellN ξ W P m (ENNReal.ofReal p)} :=
        fun ω hω => lt_of_lt_of_le hω hthn
      exact ((measure_mono hs).trans hn).trans
        (tail_const_mono hLn.le (by linarith) (min_le_right _ _) (sq_nonneg _))
    · have hs : {ω | Apos * T * LambdaN ξ W P m (ENNReal.ofReal p) *
            ellN ξ W P m (ENNReal.ofReal p) <
            T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω) 3 v z 3 1} ⊆
        {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
            ellN ξ W P m (ENNReal.ofReal p) <
            T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω) 3 v z 3 1} :=
        fun ω hω => lt_of_le_of_lt hthp hω
      exact ((measure_mono hs).trans hp').trans (by
        simpa only [mul_div_assoc] using
          (tail_const_mono hLp.le (by linarith) (min_le_right _ _) hrate))

end SupercriticalLQGUniqueness.B2.DG20Conc
