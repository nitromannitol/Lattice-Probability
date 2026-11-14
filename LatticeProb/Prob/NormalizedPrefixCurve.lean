import LatticeProb.Prob.NormalizedPathPrefix
import LatticeProb.Prob.LevyProkhorovMaps

/-! # Finite curves represented by normalized path prefixes -/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal unitInterval

namespace LatticeProb

/-- The curve class of the prefix of duration `T`. -/
noncomputable def normalizedPrefixCurve {d : ℕ}
    (w : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (T : ℝ≥0) : CurveSpace d :=
  CurveSpace.project (normalizedPathPrefix w T)

/-- The finite-prefix curve depends continuously on the path and duration. -/
theorem continuous_normalizedPrefixCurve {d : ℕ} :
    Continuous (fun p : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0 =>
      normalizedPrefixCurve p.1 p.2) :=
  CurveSpace.continuous_project.comp continuous_normalizedPathPrefix

/-- An extended duration gives a measurable curve, with infinity totalized to zero. -/
theorem measurable_normalizedPrefixCurve_toNNReal {d : ℕ} :
    Measurable (fun p : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞ =>
      normalizedPrefixCurve p.1 p.2.toNNReal) :=
  CurveSpace.continuous_project.measurable.comp measurable_normalizedPathPrefix_toNNReal

/-- The endpoint of the finite-prefix curve is the path at its duration. -/
@[simp] theorem normalizedPrefixCurve_endPoint {d : ℕ}
    (w : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (T : ℝ≥0) :
    CurveSpace.endPoint (normalizedPrefixCurve w T) = w T := by
  change normalizedPathPrefix w T 1 = w T
  change w ⟨(1 : ℝ) * (T : ℝ), _⟩ = w T
  congr 1
  apply Subtype.ext
  exact one_mul _

/-- The totalized infinite-duration curve is the constant initial-point curve. -/
theorem normalizedPrefixCurve_top {d : ℕ}
    (w : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) :
    normalizedPrefixCurve w (⊤ : ℝ≥0∞).toNNReal =
      CurveSpace.project (ContinuousMap.const unitInterval (w 0)) := by
  simp only [ENNReal.toNNReal_top, normalizedPrefixCurve]
  congr 1
  ext u
  simp only [normalizedPathPrefix_apply, NNReal.coe_zero, mul_zero,
    ContinuousMap.const_apply]
  rfl

/-- Passing from normalized representatives to their curve classes cannot increase
the Lévy–Prokhorov distance between the induced laws. -/
theorem levyProkhorovEDist_normalizedPrefixCurve_le {d : ℕ}
    (μ ν : Measure (C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞)) :
    levyProkhorovEDist
      (μ.map (fun p => normalizedPrefixCurve p.1 p.2.toNNReal))
      (ν.map (fun p => normalizedPrefixCurve p.1 p.2.toNNReal)) ≤
    levyProkhorovEDist
      (μ.map (fun p => normalizedPathPrefix p.1 p.2.toNNReal))
      (ν.map (fun p => normalizedPathPrefix p.1 p.2.toNNReal)) := by
  have h := levyProkhorovEDist_map_le_of_lipschitz_one CurveSpace.project_lipschitz
    CurveSpace.continuous_project.measurable
    (μ.map (fun p => normalizedPathPrefix p.1 p.2.toNNReal))
    (ν.map (fun p => normalizedPathPrefix p.1 p.2.toNNReal))
  simpa only [Measure.map_map CurveSpace.continuous_project.measurable
    measurable_normalizedPathPrefix_toNNReal, Function.comp_def, normalizedPrefixCurve] using h

end LatticeProb
