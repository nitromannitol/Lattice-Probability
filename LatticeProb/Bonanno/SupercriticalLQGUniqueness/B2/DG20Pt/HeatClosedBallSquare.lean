/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatClosedBallSquare at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatLocalSquareGeometry

 

set_option autoImplicit false
noncomputable section

open Set Metric
open LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_closedBall_squareCenter_subset_square {R : ℝ}
    (hR : R ≤ 1 / 2) :
    closedBall (Complex.mk (1 / 2) (1 / 2)) R ⊆ closedUnitSquare := by
  intro y hy
  have hnorm : ‖y - Complex.mk (1 / 2) (1 / 2)‖ ≤ 1 / 2 := by
    simpa only [dist_eq_norm] using (mem_closedBall.mp hy).trans hR
  have hre : |(y - Complex.mk (1 / 2) (1 / 2)).re| ≤ 1 / 2 :=
    (Complex.abs_re_le_norm _).trans hnorm
  have him : |(y - Complex.mk (1 / 2) (1 / 2)).im| ≤ 1 / 2 :=
    (Complex.abs_im_le_norm _).trans hnorm
  change |y.re - 1 / 2| ≤ 1 / 2 at hre
  change |y.im - 1 / 2| ≤ 1 / 2 at him
  change 0 ≤ y.re ∧ y.re ≤ 1 ∧ 0 ≤ y.im ∧ y.im ≤ 1
  rcases abs_le.mp hre with ⟨hreL, hreR⟩
  rcases abs_le.mp him with ⟨himL, himR⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

end SupercriticalLQGUniqueness.B2.DG20Pt
