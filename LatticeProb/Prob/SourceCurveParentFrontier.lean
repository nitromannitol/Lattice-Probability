import LatticeProb.Prob.PathClockParentFrontier
import LatticeProb.Prob.LevyProkhorovIsometricEmbedding
import LatticeProb.Topology.CurveSpaceComparison
import LatticeProb.Bonanno.BouRabeeGwynne.LevyProkhorovMaps

/-! # Parent-frontier distance and source curve laws -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set BouRabeeGwynne ReflectedGMS.GMS
open scoped NNReal ENNReal

namespace LatticeProb

/-- Frontier distance is controlled by the source-space laws of spatially
normalized path prefixes. Infinite durations are evaluated at time zero. -/
theorem levyProkhorovEDist_parentFrontier_le_sourcePathClockCurves
    (μ ν : Measure (C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) × ℝ≥0∞))
    (c : ℂ) {a : ℝ} (ha : 0 < a)
    (hμ : ∀ᵐ z ∂μ.map (fun p => Complex.orthonormalBasisOneI.repr.symm
      (p.1 p.2.toNNReal)), z ∈ frontier (ParentBlock.parentBlock c a))
    (hν : ∀ᵐ z ∂ν.map (fun p => Complex.orthonormalBasisOneI.repr.symm
      (p.1 p.2.toNNReal)), z ∈ frontier (ParentBlock.parentBlock c a)) :
    let endpoint := fun p : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) × ℝ≥0∞ =>
      Complex.orthonormalBasisOneI.repr.symm (p.1 p.2.toNNReal)
    let curve := fun p : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) × ℝ≥0∞ =>
      CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve ((affinePlaneNormalization c a).comp p.1) p.2.toNNReal)
    letI : MetricSpace MetricPlane := normalizedPlaneMetric c a ha.ne'
    let S : Set MetricPlane := MetricPlane.down ⁻¹' frontier (ParentBlock.parentBlock c a)
    levyProkhorovEDist (((μ.map endpoint).map MetricPlane.up).comap ((↑) : S → MetricPlane))
      (((ν.map endpoint).map MetricPlane.up).comap ((↑) : S → MetricPlane)) ≤
      levyProkhorovEDist (μ.map curve) (ν.map curve) := by
  let curve := fun p : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) × ℝ≥0∞ =>
    normalizedPrefixCurve ((affinePlaneNormalization c a).comp p.1) p.2.toNNReal
  have hc : Measurable curve := by
    have hp : Measurable (fun p : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) × ℝ≥0∞ =>
        ((affinePlaneNormalization c a).comp p.1, p.2)) :=
      ((ContinuousMap.continuous_postcomp (affinePlaneNormalization c a)).measurable.comp
        measurable_fst).prodMk measurable_snd
    exact measurable_normalizedPrefixCurve_toNNReal.comp hp
  let e := CurveSpaceComparison.isometryEquiv 2
  have he : MeasurableEmbedding e := e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hd := levyProkhorovEDist_map_eq_of_isometry e.isometry he (μ.map curve) (ν.map curve)
  rw [Measure.map_map he.measurable hc, Measure.map_map he.measurable hc] at hd
  have h := levyProkhorovEDist_parentFrontier_le_pathClockCurves μ ν c ha hμ hν
  exact h.trans_eq hd.symm

end LatticeProb
end
