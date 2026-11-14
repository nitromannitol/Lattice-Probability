import LatticeProb.Topology.PositivePrefixRayCost
import LatticeProb.Topology.IntervalReparamScale
import LatticeProb.Topology.ReparamEDist

/-! # Positive finite prefixes and stopped-ray distance -/

set_option autoImplicit false
open scoped ENNReal NNReal

namespace LatticeProb

/-- The distance of positive finite prefixes is bounded by the ray distance of their
constant-tail extensions. -/
theorem normalizedPrefixCurve_edist_le_reparamEDist_stopped {d : ℕ}
    (f g : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (T U : ℝ≥0)
    (hT : 0 < T) (hU : 0 < U) :
    edist (normalizedPrefixCurve f T) (normalizedPrefixCurve g U) ≤
      ReparamEDist.reparamEDist (fun t => f (min t T)) (fun t => g (min t U)) := by
  refine le_iInf fun e => ?_
  exact normalizedPrefixCurve_edist_le_stopped_ray_cost f g T U hT hU e

/-- The positive finite interval distance is bounded by the ray distance of the
constant-tail extensions. -/
theorem intervalEDist_le_reparamEDist_stopped {d : ℕ}
    (f g : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (T U : ℝ≥0)
    (hT : 0 < T) (hU : 0 < U) :
    IntervalReparamEDist.intervalEDist f g T U ≤
      ReparamEDist.reparamEDist (fun t => f (min t T)) (fun t => g (min t U)) := by
  rw [IntervalReparamEDist.intervalEDist_eq_edist_normalizedPrefixCurve f g T U hT hU]
  exact normalizedPrefixCurve_edist_le_reparamEDist_stopped f g T U hT hU

end LatticeProb
