/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaledAnnulusGeometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistFixedAnnulus
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Scale

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_image_mul_closedBall_div
    (z : ℂ) (c r : ℝ) (hr : 0 < r) :
    (fun x : ℂ => (r : ℂ) * x) '' closedBall z (c / r) =
      closedBall ((r : ℂ) * z) c := by
  have h := smul_closedBall'
    (c := (r : ℂ)) (E := ℂ) (by exact_mod_cast hr.ne') z (c / r)
  change (fun x : ℂ => (r : ℂ) * x) '' closedBall z (c / r) =
      closedBall ((r : ℂ) * z) (‖(r : ℂ)‖ * (c / r)) at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    mul_div_cancel₀ c hr.ne'] using h

theorem pt_dist_image_mul_sphere_div
    (z : ℂ) (c r : ℝ) (hr : 0 < r) :
    (fun x : ℂ => (r : ℂ) * x) '' sphere z (c / r) =
      sphere ((r : ℂ) * z) c := by
  have h := smul_sphere'
    (c := (r : ℂ)) (E := ℂ) (by exact_mod_cast hr.ne') z (c / r)
  change (fun x : ℂ => (r : ℂ) * x) '' sphere z (c / r) =
      sphere ((r : ℂ) * z) (‖(r : ℂ)‖ * (c / r)) at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    mul_div_cancel₀ c hr.ne'] using h

end SupercriticalLQGUniqueness.B2.DG20Pt
