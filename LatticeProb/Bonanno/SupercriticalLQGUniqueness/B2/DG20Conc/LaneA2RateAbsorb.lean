/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2RateAbsorb at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2CoarseRate

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneA2_loglog_rate_le_sq {T : ℝ} (hT : 3 < T) :
    Real.log (Real.log 3) *
        ((Real.log T)^2 / Real.log (Real.log T)) ≤
      (Real.log T)^2 := by
  have hlog3 : 1 < Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hll3 : 0 < Real.log (Real.log 3) := Real.log_pos hlog3
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hllT : 0 < Real.log (Real.log T) := by
    apply Real.log_pos
    exact hlog3.trans (Real.log_lt_log (by norm_num) hT)
  have hll : Real.log (Real.log 3) ≤ Real.log (Real.log T) :=
    Real.log_le_log (by linarith) (Real.log_le_log (by norm_num) hT.le)
  calc
    Real.log (Real.log 3) * ((Real.log T)^2 / Real.log (Real.log T)) ≤
        Real.log (Real.log T) *
          ((Real.log T)^2 / Real.log (Real.log T)) :=
      mul_le_mul_of_nonneg_right hll (div_nonneg (sq_nonneg _) hllT.le)
    _ = (Real.log T)^2 := by field_simp

 
theorem laneA2_two_exp {C₁ C₂ c₁ c₂ r : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hr : 0 ≤ r) :
    ENNReal.ofReal (C₁ * Real.exp (-c₁ * r)) +
      ENNReal.ofReal (C₂ * Real.exp (-c₂ * r)) ≤
      ENNReal.ofReal ((C₁ + C₂) * Real.exp (-(min c₁ c₂) * r)) := by
  have h₁ : C₁ * Real.exp (-c₁ * r) ≤
      C₁ * Real.exp (-(min c₁ c₂) * r) :=
    mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [min_le_left c₁ c₂])) hC₁
  have h₂ : C₂ * Real.exp (-c₂ * r) ≤
      C₂ * Real.exp (-(min c₁ c₂) * r) :=
    mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [min_le_right c₁ c₂])) hC₂
  calc
    _ ≤ ENNReal.ofReal (C₁ * Real.exp (-(min c₁ c₂) * r)) +
        ENNReal.ofReal (C₂ * Real.exp (-(min c₁ c₂) * r)) :=
      add_le_add (ENNReal.ofReal_le_ofReal h₁) (ENNReal.ofReal_le_ofReal h₂)
    _ = ENNReal.ofReal ((C₁ + C₂) * Real.exp (-(min c₁ c₂) * r)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end SupercriticalLQGUniqueness.B2.DG20Conc
