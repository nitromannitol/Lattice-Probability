/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistNear at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic
import LatticeProb.Bonanno.LQGMetric.LFPP.PathOps
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffSq

 





set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 





theorem pt_dist_near_le (ξ : ℝ) (hξ : 0 ≤ ξ) (φ : ℂ → ℝ)
    (U : Set ℂ) (z w : ℂ) (r A : ℝ)
    (hball : Metric.closedBall z r ⊆ U)
    (hw : dist z w ≤ r)
    (hosc : ∀ x ∈ Metric.closedBall z r, |φ x - φ z| ≤ A) :
    crossLenIn ξ φ U {z} {w} ≤
      ENNReal.ofReal (Real.exp (ξ * (φ z + A)) * dist z w) := by
  have hwr : ‖w - z‖ ≤ r := by simpa [dist_eq_norm, norm_sub_rev] using hw
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, segPath z w t ∈ U := by
    intro t ht
    apply hball
    exact (segPath_mem_closedBall z w ht).trans hwr
  have hweight : ∀ x ∈ Metric.closedBall z ‖w - z‖,
      Real.exp (ξ * φ x) ≤ Real.exp (ξ * (φ z + A)) := by
    intro x hx
    have hx' : x ∈ Metric.closedBall z r := hx.trans hwr
    have hle : φ x ≤ φ z + A := by
      have := hosc x hx'
      linarith [le_abs_self (φ x - φ z)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hle hξ)
  rw [LQGMetric.DFGPS.crossLenIn_singleton]
  calc
    lfppDOn ξ φ U z w ≤ lfppLen ξ φ (segPath z w) :=
      lfppDOn_le (isPiecewiseC1Path_segPath z w) hseg
    _ ≤ ENNReal.ofReal (Real.exp (ξ * (φ z + A)) * ‖w - z‖) :=
      lfppLen_segPath_le z w hweight
    _ = ENNReal.ofReal (Real.exp (ξ * (φ z + A)) * dist z w) := by
      congr 1
      simp [dist_eq_norm, norm_sub_rev]

end SupercriticalLQGUniqueness.B2.DG20Pt
