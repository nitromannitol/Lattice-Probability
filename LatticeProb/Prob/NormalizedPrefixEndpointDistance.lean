import LatticeProb.Prob.NormalizedPrefixCurveEndpointLaw

/-! # Endpoint distances for normalized path prefixes -/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- The distance between the endpoint laws is bounded by the distance between
the corresponding normalized finite-curve laws. -/
theorem levyProkhorovEDist_pathClockPoint_le_curve {d : ℕ}
    (μ ν : Measure (C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞)) :
    levyProkhorovEDist
      (μ.map (fun p => p.1 p.2.toNNReal))
      (ν.map (fun p => p.1 p.2.toNNReal)) ≤
    levyProkhorovEDist
      (μ.map (fun p => normalizedPrefixCurve p.1 p.2.toNNReal))
      (ν.map (fun p => normalizedPrefixCurve p.1 p.2.toNNReal)) := by
  rw [← map_endPoint_normalizedPrefixCurve μ, ← map_endPoint_normalizedPrefixCurve ν]
  exact levyProkhorovEDist_map_endPoint_le _ _

/-- The endpoint-law distance is bounded by the distance between the laws of
the normalized representative paths. -/
theorem levyProkhorovEDist_pathClockPoint_le_prefix {d : ℕ}
    (μ ν : Measure (C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞)) :
    levyProkhorovEDist
      (μ.map (fun p => p.1 p.2.toNNReal))
      (ν.map (fun p => p.1 p.2.toNNReal)) ≤
    levyProkhorovEDist
      (μ.map (fun p => normalizedPathPrefix p.1 p.2.toNNReal))
      (ν.map (fun p => normalizedPathPrefix p.1 p.2.toNNReal)) :=
  (levyProkhorovEDist_pathClockPoint_le_curve μ ν).trans
    (levyProkhorovEDist_normalizedPrefixCurve_le μ ν)

end LatticeProb
