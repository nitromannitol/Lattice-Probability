import LatticeProb.Prob.SourceCurveEndpoint
import LatticeProb.Bonanno.BouRabeeGwynne.LevyProkhorovMaps

/-! # Endpoint distance for source-curve prefixes -/

set_option autoImplicit false
noncomputable section

open MeasureTheory BouRabeeGwynne
open scoped NNReal ENNReal

namespace LatticeProb

/-- The distance between endpoint laws is bounded by the distance between
source-curve prefix laws. An infinite clock is evaluated at time zero. -/
theorem levyProkhorovEDist_pathClockEndpoints_le_sourcePrefixes {d : ℕ}
    (μ ν : Measure (C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞)) :
    levyProkhorovEDist (μ.map (fun p => p.1 p.2.toNNReal))
      (ν.map (fun p => p.1 p.2.toNNReal)) ≤
    levyProkhorovEDist
      (μ.map (fun p => CurveSpaceComparison.isometryEquiv d
        (normalizedPrefixCurve p.1 p.2.toNNReal)))
      (ν.map (fun p => CurveSpaceComparison.isometryEquiv d
        (normalizedPrefixCurve p.1 p.2.toNNReal))) := by
  have h := BouRabeeGwynne.levyProkhorovEDist_endpoint_map_le
    (μ.map (fun p => CurveSpaceComparison.isometryEquiv d
      (normalizedPrefixCurve p.1 p.2.toNNReal)))
    (ν.map (fun p => CurveSpaceComparison.isometryEquiv d
      (normalizedPrefixCurve p.1 p.2.toNNReal)))
  rw [CurveSpaceComparison.map_endPoint_sourcePrefix,
    CurveSpaceComparison.map_endPoint_sourcePrefix] at h
  exact h

end LatticeProb
end
