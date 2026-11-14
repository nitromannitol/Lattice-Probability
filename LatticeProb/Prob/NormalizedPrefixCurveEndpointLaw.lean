import LatticeProb.Prob.NormalizedPrefixCurve

/-! # Endpoint laws of normalized path prefixes -/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- The endpoint law of a normalized prefix is the law of the path evaluated
at its extended duration, with infinity totalized to zero. -/
theorem map_endPoint_normalizedPrefixCurve {d : ℕ}
    (μ : Measure (C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞)) :
    (μ.map (fun p => normalizedPrefixCurve p.1 p.2.toNNReal)).map
        CurveSpace.endPoint =
      μ.map (fun p => p.1 p.2.toNNReal) := by
  rw [Measure.map_map CurveSpace.continuous_endPoint.measurable
    measurable_normalizedPrefixCurve_toNNReal]
  congr 1
  funext p
  exact normalizedPrefixCurve_endPoint p.1 p.2.toNNReal

end LatticeProb
