/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1UpperRange at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1BoundedRange
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2RateAbsorb

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem j1_upper_range_extension
    (A CP cP : ℝ) (hA : 0 < A) (hCP : 0 < CP) (hcP : 0 < cP) :
    ∃ C' c' : ℝ, 0 < C' ∧ 0 < c' ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (K : ℕ) (hK : 64 ≤ K)
        (T : ℝ) (hT : 3 < T) (E : Set Ω),
        (Real.exp (A * Real.sqrt ((K : ℝ) + 1)) ≤ T →
          P E ≤ ENNReal.ofReal ((5 : ℝ)^K) *
            ENNReal.ofReal (CP * Real.exp
              (-cP * (Real.log T)^2 / Real.log (Real.log T)))) →
          P E ≤ ENNReal.ofReal ((5 : ℝ)^K) *
            ENNReal.ofReal (C' * Real.exp
              (-c' * (Real.log T)^2 / Real.log (Real.log T))) := by
  obtain ⟨d, hd, hbounded⟩ :=
    j1_bounded_sqrt_range hA (by norm_num : 0 ≤ (0 : ℝ))
  have hll3 : 0 < Real.log (Real.log 3) :=
    Real.log_pos (by linarith [Real.log_three_gt_d9] : 1 < Real.log 3)
  let c' := min cP (d * Real.log (Real.log 3))
  have hc' : 0 < c' := lt_min hcP (mul_pos hd hll3)
  refine ⟨CP + 1, c', by linarith, hc', ?_⟩
  intro Ω _ P _ K hK T hT E hhigh
  have hq : 0 ≤ (Real.log T)^2 / Real.log (Real.log T) :=
    div_nonneg (sq_nonneg _) (Real.log_pos
      ((by linarith [Real.log_three_gt_d9] : 1 < Real.log 3).trans
        (Real.log_lt_log (by norm_num) hT))).le
  have h5 : 0 ≤ (5 : ℝ)^K := by positivity
  have hrateP : CP * Real.exp
      (-cP * (Real.log T)^2 / Real.log (Real.log T)) ≤
      (CP + 1) * Real.exp
        (-c' * (Real.log T)^2 / Real.log (Real.log T)) := by
    have he : Real.exp (-cP * (Real.log T)^2 /
        Real.log (Real.log T)) ≤
        Real.exp (-c' * (Real.log T)^2 /
          Real.log (Real.log T)) :=
      Real.exp_le_exp.mpr (by
        have hh := mul_le_mul_of_nonneg_right
          (min_le_left cP (d * Real.log (Real.log 3))) hq
        calc
          _ = -(cP * ((Real.log T)^2 /
              Real.log (Real.log T))) := by ring
          _ ≤ -(c' * ((Real.log T)^2 /
              Real.log (Real.log T))) := neg_le_neg hh
          _ = _ := by ring)
    calc
      _ ≤ CP * Real.exp (-c' * (Real.log T)^2 /
          Real.log (Real.log T)) :=
            mul_le_mul_of_nonneg_left he hCP.le
      _ ≤ (CP + 1) * Real.exp (-c' * (Real.log T)^2 /
          Real.log (Real.log T)) := by
            nlinarith [Real.exp_pos (-c' * (Real.log T)^2 /
              Real.log (Real.log T))]
  by_cases hbig : Real.exp (A *
      Real.sqrt ((K : ℝ) + 1)) ≤ T
  · exact (hhigh hbig).trans
      (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hrateP)
        (zero_le : (0 : ℝ≥0∞) ≤ _))
  · have hsmall : T ≤ Real.exp (A *
        Real.sqrt ((K : ℝ) + 1)) := le_of_lt (lt_of_not_ge hbig)
    have h1 := hbounded K (by omega) T hT
      (by simpa only [zero_add, mul_one] using hsmall)
    have hrate : c' * ((Real.log T)^2 /
        Real.log (Real.log T)) ≤ d * (Real.log T)^2 := by
      have h1' := mul_le_mul_of_nonneg_right
        (min_le_right cP (d * Real.log (Real.log 3))) hq
      have h2 := mul_le_mul_of_nonneg_left
        (laneA2_loglog_rate_le_sq hT) hd.le
      calc
        _ ≤ (d * Real.log (Real.log 3)) *
            ((Real.log T)^2 / Real.log (Real.log T)) := h1'
        _ = d * (Real.log (Real.log 3) *
            ((Real.log T)^2 / Real.log (Real.log T))) := by ring
        _ ≤ _ := h2
    have hrateD : (5 : ℝ)^K * Real.exp (-d * (Real.log T)^2) ≤
        (5 : ℝ)^K * ((CP + 1) * Real.exp
          (-c' * (Real.log T)^2 / Real.log (Real.log T))) := by
      have he : Real.exp (-d * (Real.log T)^2) ≤
          Real.exp (-c' * (Real.log T)^2 / Real.log (Real.log T)) :=
        Real.exp_le_exp.mpr (by
          calc
            -d * (Real.log T)^2 = -(d * (Real.log T)^2) := by ring
            _ ≤ -(c' * ((Real.log T)^2 /
                Real.log (Real.log T))) := neg_le_neg hrate
            _ = _ := by ring)
      have hcoef : Real.exp (-d * (Real.log T)^2) ≤
          (CP + 1) * Real.exp
            (-c' * (Real.log T)^2 / Real.log (Real.log T)) := by
        nlinarith [Real.exp_pos
          (-c' * (Real.log T)^2 / Real.log (Real.log T))]
      exact mul_le_mul_of_nonneg_left hcoef h5
    have h1' : 1 ≤ (5 : ℝ)^K * ((CP + 1) * Real.exp
        (-c' * (Real.log T)^2 / Real.log (Real.log T))) :=
      h1.trans hrateD
    have hENN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((5 : ℝ)^K) *
        ENNReal.ofReal ((CP + 1) * Real.exp
          (-c' * (Real.log T)^2 / Real.log (Real.log T))) := by
      rw [← ENNReal.ofReal_one]
      calc
        ENNReal.ofReal (1 : ℝ) ≤
            ENNReal.ofReal ((5 : ℝ)^K * ((CP + 1) *
              Real.exp (-c' * (Real.log T)^2 /
                Real.log (Real.log T)))) :=
                  ENNReal.ofReal_le_ofReal h1'
        _ = _ := ENNReal.ofReal_mul h5
    exact (prob_le_one).trans hENN

end SupercriticalLQGUniqueness.B2.DG20Conc
