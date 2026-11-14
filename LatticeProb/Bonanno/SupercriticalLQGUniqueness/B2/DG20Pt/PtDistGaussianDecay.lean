/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistGaussianDecay at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRealTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLoopMeet
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic
import LatticeProb.Bonanno.LQGMetric.LFPP.PathOps
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAcrossGeometry
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BTight

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_gaussian_log_tail_small
    (c₀ c₁ ε : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hε : 0 < ε) :
    ∃ T : ℝ, 3 < T ∧
      c₀ * Real.exp (-c₁ * (Real.log T) ^ 2) ≤ ε := by
  let s : ℝ := max 3 (Real.log (2 * c₀ / ε) / c₁)
  have hs3 : 3 ≤ s := le_max_left _ _
  have hslog : Real.log (2 * c₀ / ε) / c₁ ≤ s := le_max_right _ _
  let T : ℝ := Real.exp s
  have hT : 3 < T := by
    have he := Real.add_one_le_exp s
    dsimp [T]
    linarith
  refine ⟨T, hT, ?_⟩
  have hsq : s ≤ s ^ 2 := by nlinarith
  have hhalf : c₀ * Real.exp (-(c₁ * s)) ≤ ε / 2 :=
    LQGMetric.DDDF.T20B.mul_exp_neg_le_half hc₀ hc₁ hε hslog
  calc
    c₀ * Real.exp (-c₁ * (Real.log T) ^ 2) =
        c₀ * Real.exp (-(c₁ * s ^ 2)) := by simp only [T, Real.log_exp]; ring
    _ ≤ c₀ * Real.exp (-(c₁ * s)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hc₀.le
    _ ≤ ε / 2 := hhalf
    _ ≤ ε := by linarith

end SupercriticalLQGUniqueness.B2.DG20Pt
