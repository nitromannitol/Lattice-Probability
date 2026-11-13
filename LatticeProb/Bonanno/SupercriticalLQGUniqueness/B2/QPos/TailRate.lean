/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.TailRate at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib

 

set_option autoImplicit false
noncomputable section

open Filter Topology

namespace SupercriticalLQGUniqueness.B2.QPos

theorem prop18_rate_tendsto_zero {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    Tendsto (fun s : ℝ => C * Real.exp (-c * s ^ 2 / Real.log s))
      atTop (𝓝 0) := by
  have hlin : Tendsto (fun s : ℝ => C * Real.exp (-c * s)) atTop (𝓝 0) := by
    have hbot : Tendsto (fun s : ℝ => -c * s) atTop atBot :=
      by simpa [Function.comp_def, neg_mul] using
        (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hc))
    simpa using (Real.tendsto_exp_atBot.comp hbot).const_mul C
  apply squeeze_zero' ?_ ?_ hlin
  · exact Filter.Eventually.of_forall fun s => mul_nonneg hC (Real.exp_pos _).le
  · filter_upwards [eventually_gt_atTop (2 : ℝ)] with s hs
    have hs0 : 0 < s := by linarith
    have hs1 : 1 < s := by linarith
    have hlog : 0 < Real.log s := Real.log_pos hs1
    have hlogs : Real.log s ≤ s := by
      have h := Real.log_le_sub_one_of_pos hs0
      linarith
    have hratio : s ≤ s ^ 2 / Real.log s := by
      apply (le_div_iff₀ hlog).2
      nlinarith
    apply mul_le_mul_of_nonneg_left _ hC
    have hm : -c * (s ^ 2 / Real.log s) ≤ -c * s :=
      mul_le_mul_of_nonpos_left hratio (by linarith : -c ≤ 0)
    apply Real.exp_le_exp.mpr
    calc
      -c * s ^ 2 / Real.log s = -c * (s ^ 2 / Real.log s) := by ring
      _ ≤ -c * s := hm

theorem prop18_rate_nat_tendsto_zero {C c κ : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hκ : 0 < κ) :
    Tendsto (fun n : ℕ =>
      ENNReal.ofReal (C * Real.exp (-c * (κ * (n : ℝ)) ^ 2 /
        Real.log (κ * (n : ℝ))))) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => κ * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hκ
  have h := (prop18_rate_tendsto_zero hC hc).comp hs
  have h' := (ENNReal.continuous_ofReal.tendsto 0).comp h
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using h'

end SupercriticalLQGUniqueness.B2.QPos
