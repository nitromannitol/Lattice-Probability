import LatticeProb.Topology.CurveSpaceComparison
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws
import LatticeProb.Prob.NormalizedPrefixCurve

/-! # Endpoints in the two finite curve spaces -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace LatticeProb.CurveSpaceComparison

/-- The canonical curve-space isometry preserves endpoints. -/
@[simp] theorem endPoint_isometryEquiv {d : ℕ} (q : CurveSpace d) :
    BouRabeeGwynne.CurveSpace.endPoint (isometryEquiv d q) = CurveSpace.endPoint q := by
  obtain ⟨f, rfl⟩ := SeparationQuotient.surjective_mk q
  rfl

/-- Pushing a curve law through the isometry preserves its endpoint law. -/
theorem map_endPoint_isometryEquiv {d : ℕ} (μ : Measure (CurveSpace d)) :
    (μ.map (isometryEquiv d)).map BouRabeeGwynne.CurveSpace.endPoint =
      μ.map CurveSpace.endPoint := by
  rw [Measure.map_map BouRabeeGwynne.CurveSpace.continuous_endPoint.measurable
    (isometryEquiv d).continuous.measurable]
  simp only [Function.comp_def, endPoint_isometryEquiv]

/-- The endpoint law of a source-space prefix is the path evaluated at its
clock, with an infinite clock evaluated at zero. -/
theorem map_endPoint_sourcePrefix {d : ℕ}
    (μ : Measure (C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞)) :
    (μ.map (fun p => isometryEquiv d (normalizedPrefixCurve p.1 p.2.toNNReal))).map
      BouRabeeGwynne.CurveSpace.endPoint = μ.map (fun p => p.1 p.2.toNNReal) := by
  change (μ.map ((isometryEquiv d) ∘ fun p =>
    normalizedPrefixCurve p.1 p.2.toNNReal)).map BouRabeeGwynne.CurveSpace.endPoint = _
  rw [Measure.map_map BouRabeeGwynne.CurveSpace.continuous_endPoint.measurable
    ((isometryEquiv d).continuous.measurable.comp measurable_normalizedPrefixCurve_toNNReal)]
  simp only [Function.comp_def, endPoint_isometryEquiv, normalizedPrefixCurve_endPoint]

end LatticeProb.CurveSpaceComparison
end
