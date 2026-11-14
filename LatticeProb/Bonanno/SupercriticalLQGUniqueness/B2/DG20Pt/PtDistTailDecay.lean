/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistTailDecay at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistChainProb
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLocalNormalizedTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateLinear
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BTight

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_loglog_tail_small
    (c₀ c₁ ε : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hε : 0 < ε) :
    ∃ T : ℝ, 3 < T ∧
      c₀ * Real.exp
        (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T)) ≤ ε := by
  obtain ⟨H, hH, hlarge⟩ :=
    pt_dist_rate_linear_large c₁ 1 hc₁ one_pos
  let s : ℝ := max H (Real.log (2 * c₀ / ε))
  have hsH : H ≤ s := le_max_left _ _
  have hslog : Real.log (2 * c₀ / ε) ≤ s := le_max_right _ _
  have hs3 : 3 ≤ s := hH.trans hsH
  let T : ℝ := Real.exp s
  have hT : 3 < T := by
    have he := Real.add_one_le_exp s
    dsimp [T]
    linarith
  refine ⟨T, hT, ?_⟩
  have hrate : s ≤ c₁ * (s ^ 2 / Real.log s) := by
    simpa only [one_mul] using hlarge s hsH
  calc
    c₀ * Real.exp
        (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T)) =
      c₀ * Real.exp (-(c₁ * (s ^ 2 / Real.log s))) := by
        simp only [T, Real.log_exp]
        congr 1
        ring_nf
    _ ≤ c₀ * Real.exp (-s) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hc₀.le
    _ ≤ ε / 2 := by
      simpa only [one_mul] using
        (LQGMetric.DDDF.T20B.mul_exp_neg_le_half
          hc₀ one_pos hε (by simpa only [div_one] using hslog))
    _ ≤ ε := by linarith

theorem pt_dist_exponential_tail_small
    (C a ε : ℝ) (hC : 0 < C) (ha : 0 < a) (hε : 0 < ε) :
    ∃ L : ℝ, 0 ≤ L ∧ C * Real.exp (-a * L) ≤ ε := by
  let L : ℝ := max 0 (Real.log (2 * C / ε) / a)
  have hL : 0 ≤ L := le_max_left _ _
  have hlog : Real.log (2 * C / ε) / a ≤ L := le_max_right _ _
  refine ⟨L, hL, ?_⟩
  have hhalf : C * Real.exp (-(a * L)) ≤ ε / 2 :=
    LQGMetric.DDDF.T20B.mul_exp_neg_le_half hC ha hε hlog
  have hh : ε / 2 ≤ ε := by linarith
  simpa only [neg_mul] using hhalf.trans hh

end SupercriticalLQGUniqueness.B2.DG20Pt
