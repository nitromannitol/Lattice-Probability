/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateMono at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaleEvent

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_log_rate_mono (L s : ℝ) (hL : 3 ≤ L) (hLs : L ≤ s) :
    L ^ 2 / Real.log L ≤ s ^ 2 / Real.log s := by
  have hL0 : 0 < L := by linarith
  have hs0 : 0 < s := by linarith
  have hlogL1 : 1 ≤ Real.log L := by
    apply le_of_lt
    apply (Real.lt_log_iff_exp_lt hL0).2
    exact lt_of_lt_of_le Real.exp_one_lt_three hL
  have hlogL : 0 < Real.log L := by linarith
  have hlogS : 0 < Real.log s := Real.log_pos (by linarith)
  have htangent : Real.log s ≤ Real.log L + (s - L) / L := by
    have h := Real.log_le_sub_one_of_pos (div_pos hs0 hL0)
    rw [Real.log_div hs0.ne' hL0.ne'] at h
    have he : s / L - 1 = (s - L) / L := by field_simp
    rw [he] at h
    linarith
  have hmult : L ^ 2 * Real.log s ≤ L ^ 2 * Real.log L + L * (s - L) := by
    have hh := mul_le_mul_of_nonneg_left htangent (sq_nonneg L)
    have he : L ^ 2 * ((s - L) / L) = L * (s - L) := by field_simp
    nlinarith
  have hfactor : 0 ≤ (s - L) * ((s + L) * Real.log L - L) := by
    apply mul_nonneg (by linarith)
    nlinarith [hlogL1]
  apply (div_le_div_iff₀ hlogL hlogS).2
  nlinarith [hmult, hfactor]

end SupercriticalLQGUniqueness.B2.DG20Pt
