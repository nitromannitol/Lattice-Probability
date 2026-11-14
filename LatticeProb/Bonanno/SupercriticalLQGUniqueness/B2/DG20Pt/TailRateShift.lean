/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.TailRateShift at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PercFieldBoundedRate

 




set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem log_div_ge_half (B T : ℝ) (hB : 1 ≤ B)
    (hT : B ^ 2 ≤ T) : Real.log T / 2 ≤ Real.log (T / B) := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hT0 : 0 < T := lt_of_lt_of_le (pow_pos hB0 2) hT
  have hlog : Real.log (B ^ 2) ≤ Real.log T :=
    Real.log_le_log (pow_pos hB0 2) hT
  rw [Real.log_pow] at hlog
  norm_num at hlog
  rw [Real.log_div hT0.ne' hB0.ne']
  linarith

 

theorem gaussian_rate_div_bound (a B T : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hT : max (9 * B) (B ^ 2) < T) :
    Real.exp (-a * (Real.log (T / B)) ^ 2) ≤
      Real.exp (-(a / 4) * (Real.log T) ^ 2) := by
  have hT2 : B ^ 2 ≤ T := (le_max_right _ _).trans hT.le
  have hT9 : 9 * B < T := (le_max_left _ _).trans_lt hT
  have hT0 : 0 < T := by nlinarith [hB]
  have hlogT : 0 ≤ Real.log T := (Real.log_nonneg (by linarith : 1 ≤ T))
  have hhalf := log_div_ge_half B T hB hT2
  have hsq : (Real.log T / 2) ^ 2 ≤ (Real.log (T / B)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by linarith)).2 hhalf
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hsq)]

 

theorem gaussian_loglog_rate_div_bound (a B T : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hT : max (9 * B) (B ^ 2) < T) :
    Real.exp (-a * (Real.log (T / B)) ^ 2 /
      Real.log (Real.log (T / B))) ≤
      Real.exp (-(a / 4) * (Real.log T) ^ 2 /
        Real.log (Real.log T)) := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hT2 : B ^ 2 ≤ T := (le_max_right _ _).trans hT.le
  have hT9 : 9 * B < T := (le_max_left _ _).trans_lt hT
  have hT0 : 0 < T := by nlinarith [hB]
  have hS9 : 9 < T / B := (lt_div_iff₀ hB0).2 hT9
  have hS0 : 0 < T / B := by linarith
  have hST : T / B ≤ T := by
    apply (div_le_iff₀ hB0).2
    nlinarith [mul_le_mul_of_nonneg_left hB hT0.le]
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith : 1 ≤ T)
  have hlogS : 1 < Real.log (T / B) :=
    (Real.lt_log_iff_exp_lt hS0).2
      (lt_trans Real.exp_one_lt_three (by linarith))
  have hlogT1 : 1 < Real.log T :=
    (Real.lt_log_iff_exp_lt hT0).2
      (lt_trans Real.exp_one_lt_three (by linarith))
  have hLLS : 0 < Real.log (Real.log (T / B)) := Real.log_pos hlogS
  have hLLT : 0 < Real.log (Real.log T) := Real.log_pos hlogT1
  have hLLle : Real.log (Real.log (T / B)) ≤ Real.log (Real.log T) :=
    Real.log_le_log (by linarith) (Real.log_le_log hS0 hST)
  have hhalf := log_div_ge_half B T hB hT2
  have hsq : (Real.log T / 2) ^ 2 ≤ (Real.log (T / B)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by linarith)).2 hhalf
  have hrate : (a / 4) * (Real.log T) ^ 2 /
      Real.log (Real.log T) ≤
      a * (Real.log (T / B)) ^ 2 /
        Real.log (Real.log (T / B)) := by
    calc
      _ = a * (Real.log T / 2) ^ 2 /
          Real.log (Real.log T) := by ring
      _ ≤ a * (Real.log (T / B)) ^ 2 /
          Real.log (Real.log T) := by
        apply div_le_div_of_nonneg_right _ hLLT.le
        exact mul_le_mul_of_nonneg_left hsq ha.le
      _ ≤ a * (Real.log (T / B)) ^ 2 /
          Real.log (Real.log (T / B)) :=
        div_le_div_of_nonneg_left (by positivity) hLLS hLLle
  apply Real.exp_le_exp.mpr
  calc
    -a * (Real.log (T / B)) ^ 2 / Real.log (Real.log (T / B)) =
        -(a * (Real.log (T / B)) ^ 2 / Real.log (Real.log (T / B))) := by ring
    _ ≤ -((a / 4) * (Real.log T) ^ 2 / Real.log (Real.log T)) := neg_le_neg hrate
    _ = -(a / 4) * (Real.log T) ^ 2 / Real.log (Real.log T) := by ring

end SupercriticalLQGUniqueness.B2.DG20Pt
