/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2LowLargeT at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2LowThreshold
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2RateAbsorb

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

private theorem low_rate_eq {ξ A M S T : ℝ}
    (hξ : 0 < ξ) (hA : 0 < A)
    (he : Real.exp (|ξ| * M) = S)
    (hlog : Real.log S = Real.log T / 2) :
    (M / A)^2 / Real.log 4 =
      (1 / (4 * ξ^2 * A^2 * Real.log 4)) * (Real.log T)^2 := by
  have hξM : ξ * M = Real.log T / 2 := by
    rw [← he, Real.log_exp] at hlog
    simpa only [abs_of_pos hξ] using hlog
  have hξ0 : ξ ≠ 0 := ne_of_gt hξ
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hlog40 : Real.log (4 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hξ0, hA0, hlog40]
  nlinarith [congrArg (fun x : ℝ => x ^ 2) hξM]

theorem laneA2_low_tails_largeT {ξ p : ℝ} (hξ : 0 < ξ)
    (hp : 0 < p) (hpHalf : p < 2⁻¹) :
    ∃ H C c : ℝ, 36 ≤ H ∧ 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (m : ℕ) (hm : m ≤ 2) (B : ℝ) (hB : 1 ≤ B)
        (T : ℝ) (hT : H < T) (v : Circle) (z : ℂ),
        P {ω | T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω) 3 v z 1 3 <
          (B^4 * T)⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} ≤
          ENNReal.ofReal (C * Real.exp (-c * (Real.log T)^2)) ∧
        P {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
            ellN ξ W P m (ENNReal.ofReal p) <
            T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω) 3 v z 3 1} ≤
          ENNReal.ofReal (C * Real.exp
            (-(c * Real.log (Real.log 3)) *
              (Real.log T)^2 / Real.log (Real.log T))) := by
  obtain ⟨E, Q, hE, hQ, hquant⟩ := laneA2_low_quantile_bounds hp hpHalf
  obtain ⟨C, A, hC, hA, hsup⟩ := laneA2_low_sup_all
  let H : ℝ := max 36 (max ((8 * E)^2) ((Q⁻¹)^2))
  let c : ℝ := 1 / (4 * ξ^2 * A^2 * Real.log 4)
  have hc : 0 < c := by dsimp [c]; positivity
  have hH : 36 ≤ H := le_max_left _ _
  refine ⟨H, C, c, hH, hC, hc, ?_⟩
  intro Ω _ P W hW m hm B hB T hT v z
  haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have h36 : 36 < T := hH.trans_lt hT
  obtain ⟨S, M, hS6, hM, hSsq, hlogS, heUp, heLow⟩ :=
    laneA2_split_parameter hξ h36
  have hS : 0 < S := by linarith
  have hS8 : 8 * E ≤ S := by
    have hh : (8 * E)^2 < S^2 := by
      rw [hSsq]
      exact ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hT
    nlinarith
  have hSQ : Q⁻¹ ≤ S := by
    have hqinv : 0 < Q⁻¹ := inv_pos.mpr hQ
    have hh : (Q⁻¹)^2 < S^2 := by
      rw [hSsq]
      exact ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hT
    nlinarith
  obtain ⟨hellE, hQle⟩ := hquant P W hW m hm
  have hpq0 : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.mpr hp
  have hpq1 : ENNReal.ofReal p < (1 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_lt_one]
    norm_num at hpHalf ⊢
    linarith
  have hell0 : 0 ≤ ellN ξ W P m (ENNReal.ofReal p) :=
    (T20B.ellN_pos hW hpq0 hpq1 m).le
  obtain ⟨hneg, hpos⟩ := laneA2_low_threshold hE hQ hB hS hSsq
    hS8 hSQ hell0 hellE hQle
  have hneg' : (B^4 * T)⁻¹ * ellN ξ W P m (ENNReal.ofReal p) ≤
      (1/8) * Real.exp (-(|ξ| * M)) := by simpa only [heLow] using hneg
  have hpos' : (3/8) * Real.exp (|ξ| * M) ≤
      T * LambdaN ξ W P m (ENNReal.ofReal p) *
        ellN ξ W P m (ENNReal.ofReal p) := by simpa only [heUp] using hpos
  obtain ⟨hlow, hupp⟩ := laneA2_low_raw hW
    (hsup P W hW) m hm B T M hM hneg' hpos' v z
  have hr : (M / A)^2 / Real.log 4 = c * (Real.log T)^2 :=
    low_rate_eq hξ hA heUp hlogS
  have hrneg : -(M / A)^2 / Real.log 4 = -c * (Real.log T)^2 := by
    rw [neg_div, hr]
    ring
  constructor
  · simpa only [hrneg] using hlow
  · have hrate := laneA2_loglog_rate_le_sq (by linarith : 3 < T)
    have hreal : C * Real.exp (-c * (Real.log T)^2) ≤
        C * Real.exp (-(c * Real.log (Real.log 3)) *
          (Real.log T)^2 / Real.log (Real.log T)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
      have hh := mul_le_mul_of_nonneg_left hrate hc.le
      have he : -c * (Real.log T)^2 ≤
          -(c * Real.log (Real.log 3)) * (Real.log T)^2 /
            Real.log (Real.log T) := by
        calc
          -c * (Real.log T)^2 = -(c * (Real.log T)^2) := by ring
          _ ≤ -(c * (Real.log (Real.log 3) *
              ((Real.log T)^2 / Real.log (Real.log T)))) := neg_le_neg hh
          _ = _ := by ring
      exact he
    rw [hrneg] at hupp
    exact hupp.trans (ENNReal.ofReal_le_ofReal hreal)

end SupercriticalLQGUniqueness.B2.DG20Conc
