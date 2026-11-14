/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCChordRatio at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCChordApprox

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Metric Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP

 

theorem laneC_chord_cost_le_of_weight_ratio
    {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ)
    {z w : ℂ} {r δ : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ)
    (hzw : ‖w - z‖ ≤ r)
    (hrel : ∀ x ∈ closedBall z r, ∀ y ∈ closedBall z r,
      Real.exp (ξ * φ x) ≤ (1 + δ) * Real.exp (ξ * φ y)) :
    lfppLen ξ φ (segPath z w) ≤
      ENNReal.ofReal (1 + δ) * lfppD ξ φ z w := by
  let E : ℂ → ℝ := fun x => Real.exp (ξ * φ x)
  have hE : Continuous E := Real.continuous_exp.comp (continuous_const.mul hφ)
  obtain ⟨y, hy, hmin⟩ := (isCompact_closedBall z r).exists_isMinOn
    ⟨z, mem_closedBall_self hr.le⟩ hE.continuousOn
  have hm : 0 < E y := Real.exp_pos _
  apply laneC_chord_cost_le_mul_distance hr hm hδ hzw
  · exact hmin
  · intro x hx
    exact hrel x (closedBall_subset_closedBall hzw hx) y hy
  · exact le_rfl

end SupercriticalLQGUniqueness.B2.DG20Conc
