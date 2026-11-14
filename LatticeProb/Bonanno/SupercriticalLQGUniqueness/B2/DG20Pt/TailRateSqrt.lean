/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.TailRateSqrt at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PercFieldReparam

 



set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem gaussian_sum_sqrt_bound
    (c₀ c₁ d₀ d₁ T : ℝ)
    (hc₀ : 0 < c₀) (hd₀ : 0 < d₀) (hT : 9 < T) :
    ENNReal.ofReal (d₀ * Real.exp (-d₁ * (Real.log (Real.sqrt T)) ^ 2)) +
      ENNReal.ofReal (c₀ * Real.exp (-c₁ * (Real.log (Real.sqrt T)) ^ 2)) ≤
    ENNReal.ofReal ((d₀ + c₀) * Real.exp
      (-(min d₁ c₁ / 4) * (Real.log T) ^ 2)) := by
  have hT0 : 0 ≤ T := by linarith
  have hlog : Real.log (Real.sqrt T) = Real.log T / 2 := Real.log_sqrt hT0
  let c : ℝ := min d₁ c₁ / 4
  have hcd : c * (Real.log T) ^ 2 ≤
      d₁ * (Real.log (Real.sqrt T)) ^ 2 := by
    rw [hlog]
    have h := mul_le_mul_of_nonneg_right (min_le_left d₁ c₁)
      (sq_nonneg (Real.log T))
    dsimp [c]
    nlinarith
  have hcc : c * (Real.log T) ^ 2 ≤
      c₁ * (Real.log (Real.sqrt T)) ^ 2 := by
    rw [hlog]
    have h := mul_le_mul_of_nonneg_right (min_le_right d₁ c₁)
      (sq_nonneg (Real.log T))
    dsimp [c]
    nlinarith
  have hd : d₀ * Real.exp (-d₁ * (Real.log (Real.sqrt T)) ^ 2) ≤
      d₀ * Real.exp (-c * (Real.log T) ^ 2) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hd₀.le
  have hc : c₀ * Real.exp (-c₁ * (Real.log (Real.sqrt T)) ^ 2) ≤
      c₀ * Real.exp (-c * (Real.log T) ^ 2) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hc₀.le
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    d₀ * Real.exp (-d₁ * (Real.log (Real.sqrt T)) ^ 2) +
        c₀ * Real.exp (-c₁ * (Real.log (Real.sqrt T)) ^ 2) ≤
      d₀ * Real.exp (-c * (Real.log T) ^ 2) +
        c₀ * Real.exp (-c * (Real.log T) ^ 2) := add_le_add hd hc
    _ = (d₀ + c₀) * Real.exp (-(min d₁ c₁ / 4) * (Real.log T) ^ 2) := by
      dsimp [c]
      ring

 




theorem gaussian_loglog_sum_sqrt_bound
    (c₀ c₁ d₀ d₁ T : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hd₀ : 0 < d₀) (hd₁ : 0 < d₁) (hT : 9 < T) :
    ENNReal.ofReal (d₀ * Real.exp (-d₁ * (Real.log (Real.sqrt T)) ^ 2)) +
      ENNReal.ofReal (c₀ * Real.exp
        (-c₁ * (Real.log (Real.sqrt T)) ^ 2 /
          Real.log (Real.log (Real.sqrt T)))) ≤
    ENNReal.ofReal ((d₀ + c₀) * Real.exp
      (-(min (d₁ * Real.log (Real.log 3)) c₁ / 4) *
        (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  have hT0 : 0 ≤ T := by linarith
  let S : ℝ := Real.sqrt T
  have hS : 3 < S := by
    dsimp [S]
    apply Real.lt_sqrt_of_sq_lt
    nlinarith
  have hS0 : 0 < S := by linarith
  have hSleT : S ≤ T := by
    have hs2 : S ^ 2 = T := Real.sq_sqrt hT0
    nlinarith
  have hlogS : 1 < Real.log S :=
    (Real.lt_log_iff_exp_lt hS0).2 (Real.exp_one_lt_three.trans hS)
  have hlogT : 1 < Real.log T :=
    (Real.lt_log_iff_exp_lt (by linarith : 0 < T)).2
      (lt_trans Real.exp_one_lt_three (by linarith : (3 : ℝ) < T))
  have hLLS : 0 < Real.log (Real.log S) := Real.log_pos hlogS
  have hLLT : 0 < Real.log (Real.log T) := Real.log_pos hlogT
  have hlogmon : Real.log S ≤ Real.log T := Real.log_le_log hS0 hSleT
  have hLLmon : Real.log (Real.log S) ≤ Real.log (Real.log T) :=
    Real.log_le_log (by linarith) hlogmon
  have hlog3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
      Real.exp_one_lt_three
  let α : ℝ := Real.log (Real.log 3)
  have hα : 0 < α := Real.log_pos hlog3
  have hαS : α ≤ Real.log (Real.log S) := by
    dsimp [α]
    apply Real.log_le_log (by linarith : 0 < Real.log 3)
    exact Real.log_le_log (by norm_num : (0 : ℝ) < 3) hS.le
  have hαT : α ≤ Real.log (Real.log T) := hαS.trans hLLmon
  have hlog : Real.log S = Real.log T / 2 := Real.log_sqrt hT0
  let c : ℝ := min (d₁ * α) c₁ / 4
  have hcd : c * (Real.log T) ^ 2 / Real.log (Real.log T) ≤
      d₁ * (Real.log S) ^ 2 := by
    have hcD : c ≤ d₁ * α / 4 :=
      div_le_div_of_nonneg_right (min_le_left (d₁ * α) c₁) (by norm_num)
    have hα' : d₁ * α / 4 ≤ d₁ * Real.log (Real.log T) / 4 := by
      gcongr
    have hcoef : c ≤ d₁ * Real.log (Real.log T) / 4 := hcD.trans hα'
    have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (Real.log T))
    apply (div_le_iff₀ hLLT).2
    rw [hlog]
    nlinarith
  have hcc : c * (Real.log T) ^ 2 / Real.log (Real.log T) ≤
      c₁ * (Real.log S) ^ 2 / Real.log (Real.log S) := by
    have hcC : c ≤ c₁ / 4 :=
      div_le_div_of_nonneg_right (min_le_right (d₁ * α) c₁) (by norm_num)
    calc
      c * (Real.log T) ^ 2 / Real.log (Real.log T) ≤
          (c₁ / 4 * (Real.log T) ^ 2) / Real.log (Real.log T) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcC (sq_nonneg (Real.log T))) hLLT.le
      _ ≤ (c₁ / 4 * (Real.log T) ^ 2) / Real.log (Real.log S) :=
        div_le_div_of_nonneg_left (by positivity) hLLS hLLmon
      _ = c₁ * (Real.log S) ^ 2 / Real.log (Real.log S) := by
        rw [hlog]
        ring
  have hd : d₀ * Real.exp (-d₁ * (Real.log S) ^ 2) ≤
      d₀ * Real.exp (-c * (Real.log T) ^ 2 / Real.log (Real.log T)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
      calc
        -d₁ * (Real.log S) ^ 2 = -(d₁ * (Real.log S) ^ 2) := by ring
        _ ≤ -(c * (Real.log T) ^ 2 / Real.log (Real.log T)) := neg_le_neg hcd
        _ = -c * (Real.log T) ^ 2 / Real.log (Real.log T) := by ring)) hd₀.le
  have hc : c₀ * Real.exp
      (-c₁ * (Real.log S) ^ 2 / Real.log (Real.log S)) ≤
      c₀ * Real.exp (-c * (Real.log T) ^ 2 / Real.log (Real.log T)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
      calc
        -c₁ * (Real.log S) ^ 2 / Real.log (Real.log S) =
            -(c₁ * (Real.log S) ^ 2 / Real.log (Real.log S)) := by ring
        _ ≤ -(c * (Real.log T) ^ 2 / Real.log (Real.log T)) := neg_le_neg hcc
        _ = -c * (Real.log T) ^ 2 / Real.log (Real.log T) := by ring)) hc₀.le
  dsimp only [S] at hd hc
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    d₀ * Real.exp (-d₁ * (Real.log (Real.sqrt T)) ^ 2) +
        c₀ * Real.exp
          (-c₁ * (Real.log (Real.sqrt T)) ^ 2 /
            Real.log (Real.log (Real.sqrt T))) ≤
      d₀ * Real.exp (-c * (Real.log T) ^ 2 / Real.log (Real.log T)) +
        c₀ * Real.exp (-c * (Real.log T) ^ 2 / Real.log (Real.log T)) :=
      add_le_add hd hc
    _ = (d₀ + c₀) * Real.exp
        (-(min (d₁ * Real.log (Real.log 3)) c₁ / 4) *
          (Real.log T) ^ 2 / Real.log (Real.log T)) := by
      dsimp [c, α]
      ring

end SupercriticalLQGUniqueness.B2.DG20Pt
