/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Lim.FiniteCircleAnnulusLower at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: `convert hscale using 1` already closes the left-hand goal, so the `rfl` bullet after it is removed (one proof line).
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Lim.FiniteAnnulusCover
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.Disconnects
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.LiminfLimsup
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import LatticeProb.Bonanno.LQGMetric.Metric.InternalLimitC
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Lim.FiniteLFPP

 


set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem normalized_annulus_cross_le_point_distance
    (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    (z u v : ℂ) (d : ℝ)
    (hu : dist u z < d / 16) (hv : 3 * d / 4 < dist v z)
    (hd : 0 < d) :
    ENNReal.ofReal (a : ℝ)⁻¹ *
      crossLenIn ξ φ (closedBall z d) (sphere z (d / 16))
        (sphere z (3 * d / 4)) ≤
      ENNReal.ofReal ((normalizedContLFPP ξ a φ).1 (u, v)) := by
  have hcross := annulus_cross_le_lfppDOn ξ φ z u v
    (d / 16) (3 * d / 4) d hu (by linarith) (by linarith) hv
  have hscale := mul_le_mul_of_nonneg_left hcross bot_le
    (a := ENNReal.ofReal (a : ℝ)⁻¹)
  convert hscale using 1
  rw [normalizedContLFPP, ContMetric.smulPos_apply,
    lfppContMetric_apply]
  rw [ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr a.property))]
  rw [ENNReal.ofReal_toReal (lfppD_ne_top φ.continuous u v)]

end SupercriticalLQGUniqueness.B2.DG20Lim
