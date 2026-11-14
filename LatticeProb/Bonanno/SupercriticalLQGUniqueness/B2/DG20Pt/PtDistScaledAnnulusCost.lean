/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaledAnnulusCost at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaledAnnulusGeometry

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_scaled_annulus_cross_cost
    (ξ : ℝ) (g : ℂ → ℝ) (z : ℂ)
    (d r : ℝ) (hr : 0 < r) :
    ENNReal.ofReal r *
      crossLenIn ξ (fun x => g ((r : ℂ) * x))
        (closedBall z ((3 * d / 4) / r))
        (sphere z ((d / 4) / r))
        (sphere z ((d / 2) / r)) =
      crossLenIn ξ g
        (closedBall ((r : ℂ) * z) (3 * d / 4))
        (sphere ((r : ℂ) * z) (d / 4))
        (sphere ((r : ℂ) * z) (d / 2)) := by
  have h := crossLenIn_image_mul ξ g
    (closedBall z ((3 * d / 4) / r))
    (sphere z ((d / 4) / r))
    (sphere z ((d / 2) / r)) hr
  rw [pt_dist_image_mul_closedBall_div z (3 * d / 4) r hr,
    pt_dist_image_mul_sphere_div z (d / 4) r hr,
    pt_dist_image_mul_sphere_div z (d / 2) r hr] at h
  exact h.symm

end SupercriticalLQGUniqueness.B2.DG20Pt
