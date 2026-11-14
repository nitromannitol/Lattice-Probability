/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2ShiftRates at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2ShiftLower

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem laneA2_shifted_lower_tail_rate {D T C c : ℝ}
    (hD : 1 ≤ D) (hT : max (3 * D) (D^2) < T)
    (hC : 0 ≤ C) (hc : 0 < c) :
    C * Real.exp (-c * (Real.log (T / D))^2) ≤
      C * Real.exp (-(c / 4) * (Real.log T)^2) := by
  obtain ⟨_, hrate⟩ := laneA2_shifted_sq_rate hD hT
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
  nlinarith [mul_le_mul_of_nonneg_left hrate hc.le]

theorem laneA2_shifted_upper_tail_rate {D₁ D₂ T C₁ C₂ c₁ c₂ : ℝ}
    (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂)
    (hT₁ : max (3 * D₁) (D₁^2) < T)
    (hT₂ : max (3 * D₂) (D₂^2) < T)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    C₁ * Real.exp (-c₁ * (Real.log (T / D₁))^2 /
      Real.log (Real.log (T / D₁))) +
    C₂ * Real.exp (-c₂ * (Real.log (T / D₂))^2 /
      Real.log (Real.log (T / D₂))) ≤
    (C₁ + C₂) * Real.exp (-(min c₁ c₂ / 4) *
      (Real.log T)^2 / Real.log (Real.log T)) := by
  have hT3 : 3 < T := by
    have hh : 3 * D₁ < T := (le_max_left _ _).trans_lt hT₁
    nlinarith
  have hloglog : 0 < Real.log (Real.log T) := by
    have hlog3 : 1 < Real.log 3 := by linarith [Real.log_three_gt_d9]
    exact Real.log_pos (hlog3.trans (Real.log_lt_log (by norm_num) hT3))
  have hr : 0 ≤ (Real.log T)^2 / Real.log (Real.log T) :=
    div_nonneg (sq_nonneg _) hloglog.le
  have hshift₁ := laneA_shifted_log_rate hD₁ hT₁
  have hshift₂ := laneA_shifted_log_rate hD₂ hT₂
  have hr4 : 0 ≤ (Real.log T)^2 /
      (4 * Real.log (Real.log T)) := by positivity
  have hbase₁ : (min c₁ c₂ / 4) * (Real.log T)^2 /
      Real.log (Real.log T) ≤
      c₁ * (Real.log (T / D₁))^2 /
        Real.log (Real.log (T / D₁)) := by
    have hb := mul_le_mul_of_nonneg_right (min_le_left c₁ c₂) hr4
    have ha := mul_le_mul_of_nonneg_left hshift₁ hc₁.le
    calc
      _ = min c₁ c₂ * ((Real.log T)^2 /
          (4 * Real.log (Real.log T))) := by ring
      _ ≤ c₁ * ((Real.log T)^2 /
          (4 * Real.log (Real.log T))) := hb
      _ ≤ c₁ * ((Real.log (T / D₁))^2 /
          Real.log (Real.log (T / D₁))) := ha
      _ = _ := by ring
  have hbase₂ : (min c₁ c₂ / 4) * (Real.log T)^2 /
      Real.log (Real.log T) ≤
      c₂ * (Real.log (T / D₂))^2 /
        Real.log (Real.log (T / D₂)) := by
    have hb := mul_le_mul_of_nonneg_right (min_le_right c₁ c₂) hr4
    have ha := mul_le_mul_of_nonneg_left hshift₂ hc₂.le
    calc
      _ = min c₁ c₂ * ((Real.log T)^2 /
          (4 * Real.log (Real.log T))) := by ring
      _ ≤ c₂ * ((Real.log T)^2 /
          (4 * Real.log (Real.log T))) := hb
      _ ≤ c₂ * ((Real.log (T / D₂))^2 /
          Real.log (Real.log (T / D₂))) := ha
      _ = _ := by ring
  have hrate₁ : -c₁ * (Real.log (T / D₁))^2 /
      Real.log (Real.log (T / D₁)) ≤
      -(min c₁ c₂ / 4) * (Real.log T)^2 /
        Real.log (Real.log T) := by
    calc
      _ = -(c₁ * (Real.log (T / D₁))^2 /
          Real.log (Real.log (T / D₁))) := by ring
      _ ≤ -((min c₁ c₂ / 4) * (Real.log T)^2 /
          Real.log (Real.log T)) := neg_le_neg hbase₁
      _ = _ := by ring
  have hrate₂ : -c₂ * (Real.log (T / D₂))^2 /
      Real.log (Real.log (T / D₂)) ≤
      -(min c₁ c₂ / 4) * (Real.log T)^2 /
        Real.log (Real.log T) := by
    calc
      _ = -(c₂ * (Real.log (T / D₂))^2 /
          Real.log (Real.log (T / D₂))) := by ring
      _ ≤ -((min c₁ c₂ / 4) * (Real.log T)^2 /
          Real.log (Real.log T)) := neg_le_neg hbase₂
      _ = _ := by ring
  have h₁ : C₁ * Real.exp (-c₁ * (Real.log (T / D₁))^2 /
      Real.log (Real.log (T / D₁))) ≤
      C₁ * Real.exp (-(min c₁ c₂ / 4) *
        (Real.log T)^2 / Real.log (Real.log T)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrate₁) hC₁
  have h₂ : C₂ * Real.exp (-c₂ * (Real.log (T / D₂))^2 /
      Real.log (Real.log (T / D₂))) ≤
      C₂ * Real.exp (-(min c₁ c₂ / 4) *
        (Real.log T)^2 / Real.log (Real.log T)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrate₂) hC₂
  calc
    _ ≤ C₁ * Real.exp (-(min c₁ c₂ / 4) *
        (Real.log T)^2 / Real.log (Real.log T)) +
      C₂ * Real.exp (-(min c₁ c₂ / 4) *
        (Real.log T)^2 / Real.log (Real.log T)) := add_le_add h₁ h₂
    _ = _ := by ring

end SupercriticalLQGUniqueness.B2.DG20Conc
