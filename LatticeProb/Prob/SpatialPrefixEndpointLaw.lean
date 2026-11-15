import LatticeProb.Prob.NormalizedPrefixCurveEndpointLaw

/-! # Endpoint laws of spatially transformed path prefixes -/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- The endpoint of a spatially transformed prefix has the transformed endpoint
law. Infinite durations are totalized to zero on both sides. -/
theorem map_endPoint_spatial_normalizedPrefixCurve {d : ℕ}
    (F : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin d)))
    (μ : Measure (C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞)) :
    (μ.map (fun p => normalizedPrefixCurve (F.comp p.1) p.2.toNNReal)).map
        CurveSpace.endPoint =
      (μ.map (fun p => p.1 p.2.toNNReal)).map F := by
  have hpath : Measurable (fun p : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞ =>
      (F.comp p.1, p.2)) :=
    ((ContinuousMap.continuous_postcomp F).measurable.comp measurable_fst).prodMk measurable_snd
  have hcurve : Measurable (fun p : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞ =>
      normalizedPrefixCurve (F.comp p.1) p.2.toNNReal) :=
    measurable_normalizedPrefixCurve_toNNReal.comp hpath
  have heval : Measurable (fun p : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞ =>
      p.1 p.2.toNNReal) := by
    simpa only [normalizedPrefixCurve_endPoint, Function.comp_def] using
      CurveSpace.continuous_endPoint.measurable.comp measurable_normalizedPrefixCurve_toNNReal
  rw [Measure.map_map CurveSpace.continuous_endPoint.measurable hcurve,
    Measure.map_map F.continuous.measurable heval]
  congr 1
  funext p
  exact normalizedPrefixCurve_endPoint (F.comp p.1) p.2.toNNReal

end LatticeProb
