/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistTerminal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistNear

 


set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_terminal_to_crossing (ξ : ℝ) (hξ : 0 ≤ ξ)
    (φ : ℂ → ℝ) (U : Set ℂ) (z x u : ℂ) (r A : ℝ)
    (hr : 0 < r) (hzx : dist z x < r / 4)
    (hu : u ∈ sphere x (r / 4))
    (hball : closedBall z r ⊆ U)
    (hosc : ∀ v ∈ closedBall z r, |φ v - φ z| ≤ A) :
    lfppDOn ξ φ U z u ≤
      ENNReal.ofReal (Real.exp (ξ * (φ z + A)) * (r / 2)) := by
  have hhalf : dist z u ≤ r / 2 := by
    have ht := dist_triangle z x u
    rw [mem_sphere] at hu
    rw [dist_comm x u] at ht
    linarith
  have hzu : dist z u ≤ r := by linarith
  have hreal : 0 ≤ Real.exp (ξ * (φ z + A)) := (Real.exp_pos _).le
  have hbound := pt_dist_near_le ξ hξ φ U z u r A hball hzu hosc
  rw [LQGMetric.DFGPS.crossLenIn_singleton] at hbound
  exact hbound.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hhalf hreal))

end SupercriticalLQGUniqueness.B2.DG20Pt
