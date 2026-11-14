/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseRate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseDenominator
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseParameter

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem j1_coarse_log_sq_lower (ξ B T M : ℝ)
    (hB : 0 ≤ B) (hT : 0 < T) (hM : 0 < M)
    (hD : (1 + |ξ| * B)^2 ≤ M) :
    (Real.log T)^2 / M ≤
      (Real.log (j1CoarseTailParameter ξ B T))^2 := by
  have hd : 0 < 1 + |ξ| * B := by positivity
  rw [j1_coarse_parameter_log ξ B T hB hT]
  have hd2 : 0 < (1 + |ξ| * B)^2 := sq_pos_of_pos hd
  have hsq : (Real.log T / (1 + |ξ| * B))^2 =
      (Real.log T)^2 / (1 + |ξ| * B)^2 := by rw [div_pow]
  rw [hsq]
  apply (div_le_div_iff₀ hM hd2).mpr
  nlinarith [mul_nonneg (sq_nonneg (Real.log T)) (sub_nonneg.mpr hD)]

theorem j1_coarse_exp_lower (ξ B T M c : ℝ)
    (hB : 0 ≤ B) (hT : 0 < T) (hM : 0 < M)
    (hc : 0 ≤ c) (hD : (1 + |ξ| * B)^2 ≤ M) :
    Real.exp (-c * (Real.log (j1CoarseTailParameter ξ B T))^2) ≤
      Real.exp (-c * (Real.log T)^2 / M) := by
  apply Real.exp_le_exp.mpr
  have hlog := j1_coarse_log_sq_lower ξ B T M hB hT hM hD
  have hmul := mul_le_mul_of_nonneg_left hlog hc
  calc
    -c * (Real.log (j1CoarseTailParameter ξ B T))^2 =
        -(c * (Real.log (j1CoarseTailParameter ξ B T))^2) := by ring
    _ ≤ -(c * ((Real.log T)^2 / M)) := neg_le_neg hmul
    _ = -c * (Real.log T)^2 / M := by ring

theorem j1_coarse_loglog_rate_lower (ξ B T M : ℝ)
    (hB : 0 ≤ B) (hT : 0 < T) (hM : 0 < M)
    (hD : (1 + |ξ| * B)^2 ≤ M)
    (hs : 3 < j1CoarseTailParameter ξ B T) :
    (Real.log T)^2 / (M * Real.log (Real.log T)) ≤
      (Real.log (j1CoarseTailParameter ξ B T))^2 /
        Real.log (Real.log (j1CoarseTailParameter ξ B T)) := by
  let s := j1CoarseTailParameter ξ B T
  have hD1 : 1 ≤ 1 + |ξ| * B := by
    nlinarith [mul_nonneg (abs_nonneg ξ) hB]
  have hd : 0 < 1 + |ξ| * B := by linarith
  have hT1 : 1 ≤ T := by
    by_contra h
    have ht1 : T ≤ 1 := le_of_not_ge h
    have hsle : s ≤ 1 := Real.rpow_le_one hT.le ht1
      (div_nonneg (by norm_num) hd.le)
    change s ≤ 1 at hsle
    linarith
  have hExp : 1 / (1 + |ξ| * B) ≤ 1 := by
    apply (div_le_iff₀ hd).2
    nlinarith
  have hsT : s ≤ T := by
    exact Real.rpow_le_self_of_one_le hT1 hExp
  have hlogST : Real.log s ≤ Real.log T := Real.log_le_log (by linarith [hs]) hsT
  have hlls : 0 < Real.log (Real.log s) :=
    Real.log_pos (by
      have h3 : (1 : ℝ) < Real.log 3 := by
        linarith [Real.log_three_gt_d9]
      exact h3.trans (Real.log_lt_log (by norm_num) hs))
  have hlogs : 1 < Real.log s := by
    have h3 : (1 : ℝ) < Real.log 3 := by
      linarith [Real.log_three_gt_d9]
    exact h3.trans (Real.log_lt_log (by norm_num) hs)
  have hlogt : 1 < Real.log T := hlogs.trans_le hlogST
  have hllt : 0 < Real.log (Real.log T) :=
    Real.log_pos hlogt
  have hll : Real.log (Real.log s) ≤ Real.log (Real.log T) :=
    Real.log_le_log (by linarith [hlogs]) hlogST
  have hnum := j1_coarse_log_sq_lower ξ B T M hB hT hM hD
  have hmul : ((Real.log T)^2 / M) * Real.log (Real.log s) ≤
      (Real.log s)^2 * Real.log (Real.log T) := by
    calc
      _ ≤ (Real.log s)^2 * Real.log (Real.log s) :=
        mul_le_mul_of_nonneg_right hnum hlls.le
      _ ≤ (Real.log s)^2 * Real.log (Real.log T) :=
        mul_le_mul_of_nonneg_left hll (sq_nonneg _)
  have hquot := (div_le_div_iff₀ hllt hlls).mpr hmul
  have he : (Real.log T)^2 / M / Real.log (Real.log T) =
      (Real.log T)^2 / (M * Real.log (Real.log T)) := by
    field_simp [ne_of_gt hM, ne_of_gt hllt]
  rw [← he]
  exact hquot

theorem j1_coarse_exp_loglog_lower (ξ B T M c : ℝ)
    (hB : 0 ≤ B) (hT : 0 < T) (hM : 0 < M)
    (hc : 0 ≤ c) (hD : (1 + |ξ| * B)^2 ≤ M)
    (hs : 3 < j1CoarseTailParameter ξ B T) :
    Real.exp (-c * (Real.log (j1CoarseTailParameter ξ B T))^2 /
      Real.log (Real.log (j1CoarseTailParameter ξ B T))) ≤
      Real.exp (-c * (Real.log T)^2 /
        (M * Real.log (Real.log T))) := by
  apply Real.exp_le_exp.mpr
  have hrate := j1_coarse_loglog_rate_lower ξ B T M hB hT hM hD hs
  have hmul := mul_le_mul_of_nonneg_left hrate hc
  calc
    -c * (Real.log (j1CoarseTailParameter ξ B T))^2 /
        Real.log (Real.log (j1CoarseTailParameter ξ B T)) =
      -(c * ((Real.log (j1CoarseTailParameter ξ B T))^2 /
        Real.log (Real.log (j1CoarseTailParameter ξ B T)))) := by ring
    _ ≤ -(c * ((Real.log T)^2 /
        (M * Real.log (Real.log T)))) := neg_le_neg hmul
    _ = -c * (Real.log T)^2 /
        (M * Real.log (Real.log T)) := by ring

end SupercriticalLQGUniqueness.B2.DG20Conc
