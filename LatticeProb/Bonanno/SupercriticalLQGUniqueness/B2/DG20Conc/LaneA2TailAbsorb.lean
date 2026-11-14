/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2TailAbsorb at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2RateAbsorb

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
theorem laneA2_lower_tail_absorb
    {ξ A Cg Cu cu S M T : ℝ} (hξ : 0 < ξ) (hA : 0 < A)
    (hCg : 0 ≤ Cg) (hCu : 0 ≤ Cu)
    (he : Real.exp (|ξ| * M) = S)
    (hlog : Real.log S = Real.log T / 2) :
    ENNReal.ofReal (Cg * Real.exp (-((M / A)^2 * 3 / Real.log 4))) +
      ENNReal.ofReal (Cu * Real.exp (-cu * (Real.log S)^2)) ≤
      ENNReal.ofReal ((Cg + Cu) * Real.exp
        (-(min (3 / (4 * ξ^2 * A^2 * Real.log 4)) (cu / 4)) *
          (Real.log T)^2)) := by
  have hG := laneA2_coarse_rate_eq hξ hA he hlog
  have hU : -cu * (Real.log S)^2 = -(cu / 4) * (Real.log T)^2 := by
    rw [hlog]
    ring
  rw [hG, hU]
  simpa only [neg_mul] using
    (laneA2_two_exp (c₁ := 3 / (4 * ξ^2 * A^2 * Real.log 4))
      (c₂ := cu / 4) hCg hCu (sq_nonneg (Real.log T)))

 
theorem laneA2_upper_tail_absorb
    {ξ A Cg Cu cu S M T : ℝ} (hξ : 0 < ξ) (hA : 0 < A)
    (hCg : 0 ≤ Cg) (hCu : 0 ≤ Cu) (hcu : 0 ≤ cu)
    (hS : 6 < S) (hSsq : S ^ 2 = T)
    (he : Real.exp (|ξ| * M) = S)
    (hlog : Real.log S = Real.log T / 2) :
    ENNReal.ofReal (Cg * Real.exp (-((M / A)^2 * 3 / Real.log 4))) +
      ENNReal.ofReal (Cu * Real.exp
        (-cu * (Real.log (S / 2))^2 / Real.log (Real.log (S / 2)))) ≤
      ENNReal.ofReal ((Cg + Cu) * Real.exp
        (-(min ((3 / (4 * ξ^2 * A^2 * Real.log 4)) *
          Real.log (Real.log 3)) (cu / 16)) *
          ((Real.log T)^2 / Real.log (Real.log T)))) := by
  let q : ℝ := (Real.log T)^2 / Real.log (Real.log T)
  let cg : ℝ := 3 / (4 * ξ^2 * A^2 * Real.log 4)
  let k : ℝ := Real.log (Real.log 3)
  have hT : 3 < T := by rw [← hSsq]; nlinarith
  have hlog3 : 1 < Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hllT : 0 < Real.log (Real.log T) := by
    apply Real.log_pos
    exact hlog3.trans (Real.log_lt_log (by norm_num) hT)
  have hq : 0 ≤ q := div_nonneg (sq_nonneg _) hllT.le
  have hcg : 0 ≤ cg := by
    dsimp [cg]
    positivity
  have hgrate : cg * k * q ≤ (M / A)^2 * 3 / Real.log 4 := by
    rw [laneA2_coarse_rate_eq hξ hA he hlog]
    simpa only [cg, k, q, mul_assoc] using
      (mul_le_mul_of_nonneg_left (laneA2_loglog_rate_le_sq hT) hcg)
  have hurate : (cu / 16) * q ≤
      cu * ((Real.log (S / 2))^2 / Real.log (Real.log (S / 2))) := by
    have hr := laneA2_sqrt_shifted_log_rate hS hSsq hlog
    have hc := mul_le_mul_of_nonneg_left hr hcu
    calc
      (cu / 16) * q = cu *
          ((Real.log T)^2 / (16 * Real.log (Real.log T))) := by dsimp [q]; ring
      _ ≤ _ := hc
  have hG : Cg * Real.exp (-((M / A)^2 * 3 / Real.log 4)) ≤
      Cg * Real.exp (-(cg * k) * q) :=
    mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [hgrate])) hCg
  have hU : Cu * Real.exp
      (-cu * (Real.log (S / 2))^2 / Real.log (Real.log (S / 2))) ≤
      Cu * Real.exp (-(cu / 16) * q) := by
    have heU : -cu * (Real.log (S / 2))^2 / Real.log (Real.log (S / 2)) =
        -(cu * ((Real.log (S / 2))^2 / Real.log (Real.log (S / 2)))) := by ring
    rw [heU]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by simpa only [neg_mul] using (neg_le_neg hurate))) hCu
  calc
    _ ≤ ENNReal.ofReal (Cg * Real.exp (-(cg * k) * q)) +
        ENNReal.ofReal (Cu * Real.exp (-(cu / 16) * q)) :=
      add_le_add (ENNReal.ofReal_le_ofReal hG) (ENNReal.ofReal_le_ofReal hU)
    _ ≤ ENNReal.ofReal ((Cg + Cu) * Real.exp (-(min (cg * k) (cu / 16)) * q)) := by
      simpa only [neg_mul] using
        (laneA2_two_exp (c₁ := cg * k) (c₂ := cu / 16) hCg hCu hq)
    _ = _ := rfl

end SupercriticalLQGUniqueness.B2.DG20Conc
