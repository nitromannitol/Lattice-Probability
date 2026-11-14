import LatticeProb.Topology.UnboundedRayIntervalIntegrand
import LatticeProb.Prob.BallExitRadius

/-! # Almost-everywhere regularity of ball exit radii -/

set_option autoImplicit false

open MeasureTheory Metric
open scoped ENNReal NNReal Topology

namespace LatticeProb.UnboundedRayIntervalIntegrand

/-- For almost every radius the ball exit clock is continuous, and the radius is
    different from the initial distance to the origin. -/
theorem ae_ballClock_continuousAt_and_ne_initial {d : ℕ} (f : Path d) :
    ∀ᵐ r : ℝ ∂volume, ContinuousAt (fun s : ℝ => ballClock f s) r ∧
      r ≠ dist (f 0) 0 := by
  have hc : ∀ᵐ r : ℝ ∂volume, ContinuousAt (fun s : ℝ => ballClock f s) r :=
    ae_continuousAt_openExitTime_ball_radius (fun t (g : Path d) => g t) f 0
  have hn : ∀ᵐ r : ℝ ∂volume, r ≠ dist (f 0) 0 := Measure.ae_ne volume _
  exact hc.and hn

end LatticeProb.UnboundedRayIntervalIntegrand
