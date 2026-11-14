/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBScaleCutoff at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiField
import Mathlib.Analysis.SpecialFunctions.Log.Base

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

 
def laneBCoarseIndex (Q : PsiParams) (K : ℕ) : ℕ :=
  Nat.ceil (Real.logb 2 ((K : ℝ) ^ Q.ε₀))

 
theorem laneB_coarseIndex_radius (Q : PsiParams) (K : ℕ) (hK : 2 ≤ K) :
    (2 : ℝ) ^ ((laneBCoarseIndex Q K : ℝ) - 1) < (K : ℝ) ^ Q.ε₀ ∧
    (K : ℝ) ^ Q.ε₀ ≤ (2 : ℝ) ^ (laneBCoarseIndex Q K : ℝ) := by
  have hK1 : (1 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hK)
  have hx : 0 < (K : ℝ) ^ Q.ε₀ := Real.rpow_pos_of_pos (by linarith) _
  have hlog : 0 ≤ Real.logb 2 ((K : ℝ) ^ Q.ε₀) :=
    (Real.logb_nonneg_iff (by norm_num : (1 : ℝ) < 2) hx).2
      (le_of_lt (Real.one_lt_rpow hK1 Q.ε₀_pos))
  have hlo : (laneBCoarseIndex Q K : ℝ) - 1 <
      Real.logb 2 ((K : ℝ) ^ Q.ε₀) := by
    have h := Nat.ceil_lt_add_one hlog
    dsimp [laneBCoarseIndex] at *
    linarith
  have hhi : Real.logb 2 ((K : ℝ) ^ Q.ε₀) ≤
      (laneBCoarseIndex Q K : ℝ) := by
    exact Nat.le_ceil _
  constructor
  · exact (Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 2) hx).mp hlo
  · exact (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hx).mp hhi

end SupercriticalLQGUniqueness.B2.DG20Conc
