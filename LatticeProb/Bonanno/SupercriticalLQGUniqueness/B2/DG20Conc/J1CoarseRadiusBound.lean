/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseRadiusBound at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBScaleCutoff

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.WhiteNoise

theorem j1_coarse_radius_lt_four_power (Q : PsiParams) (K : ℕ)
    (hK : 2 ≤ K) :
    (2 : ℝ)^(laneBCoarseIndex Q K + 1) < 4 * (K : ℝ)^Q.ε₀ := by
  have hlo := (laneB_coarseIndex_radius Q K hK).1
  let m := laneBCoarseIndex Q K
  have he : (2 : ℝ)^((m : ℝ) - 1) = (2 : ℝ)^m / 2 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast]
    norm_num
  rw [he] at hlo
  have he2 : (2 : ℝ)^(m + 1) = 2 * (2 : ℝ)^m := by
    rw [pow_succ]
    ring
  rw [he2]
  linarith

end SupercriticalLQGUniqueness.B2.DG20Conc
