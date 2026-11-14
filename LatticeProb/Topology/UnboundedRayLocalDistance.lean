import LatticeProb.Topology.UnboundedRayIntervalIntegrand
import Mathlib.MeasureTheory.Integral.Prod

/-! # Local interval distance on unbounded rays -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb.UnboundedRayLocalDistance

open UnboundedRayIntervalIntegrand LocalCurveIntervalDistance

variable {d : ℕ}

/-- First exit from a ball for a not necessarily continuous ray. -/
noncomputable def rayClock (f : ℝ≥0 → EuclideanSpace ℝ (Fin d)) (r : ℝ) : ℝ≥0∞ :=
  openExitTime (fun t f => f t) (ball 0 r) f

/-- The local interval distance on continuous rays with unbounded range. -/
noncomputable def localEDist (f g : UnboundedRay d) : ℝ≥0∞ :=
  LocalCurveIntervalDistance.localEDist rayClock f.1 g.1

@[simp] theorem localEDist_self (f : UnboundedRay d) : localEDist f f = 0 :=
  LocalCurveIntervalDistance.localEDist_self rayClock f.1

theorem localEDist_comm (f g : UnboundedRay d) : localEDist f g = localEDist g f :=
  LocalCurveIntervalDistance.localEDist_comm rayClock f.1 g.1

/-- The local interval distance is jointly Borel measurable. -/
theorem measurable_localEDist : Measurable (fun p : UnboundedRay d × UnboundedRay d =>
    localEDist p.1 p.2) := by
  exact Measurable.lintegral_prod_right' (ν := volume.restrict (Ioi (1 : ℝ)))
    measurable_weighted_intervalEDist

/-- The local interval distance satisfies the triangle inequality. -/
theorem localEDist_triangle (f g h : UnboundedRay d) :
    localEDist f h ≤ localEDist f g + localEDist g h := by
  apply LocalCurveIntervalDistance.localEDist_triangle
  have hm := measurable_weighted_intervalEDist (d := d)
  have hp : Measurable (fun r : ℝ => ((f, g), r)) := measurable_const.prodMk measurable_id
  exact (hm.comp hp).aemeasurable

end LatticeProb.UnboundedRayLocalDistance
