import LatticeProb.Prob.SpatialPrefixEndpointLaw
import LatticeProb.Prob.ParentFrontierCurveDistance

/-! # Parent-frontier distance for path-clock laws -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set BouRabeeGwynne ReflectedGMS.GMS
open scoped NNReal ENNReal

namespace LatticeProb

/-- The affine normalization of the plane, expressed in Euclidean coordinates. -/
def affinePlaneNormalization (c : ℂ) (a : ℝ) :
    C(EuclideanSpace ℝ (Fin 2), EuclideanSpace ℝ (Fin 2)) :=
  ⟨fun x => Complex.orthonormalBasisOneI.repr
      ((Complex.orthonormalBasisOneI.repr.symm x - c) / (a : ℂ)), by fun_prop⟩

/-- The normalized complex endpoint law is the endpoint law of the spatially
normalized prefix, in Euclidean coordinates. Infinite clocks use time zero. -/
theorem map_affine_pathClock_endpoint (μ : Measure
    (C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) × ℝ≥0∞)) (c : ℂ) (a : ℝ) :
    (μ.map (fun p => Complex.orthonormalBasisOneI.repr.symm
      (p.1 p.2.toNNReal))).map (fun z : ℂ => (z - c) / (a : ℂ)) =
    ((μ.map (fun p => normalizedPrefixCurve
      ((affinePlaneNormalization c a).comp p.1) p.2.toNNReal)).map
        CurveSpace.endPoint).map Complex.orthonormalBasisOneI.repr.symm := by
  rw [map_endPoint_spatial_normalizedPrefixCurve]
  have heval : Measurable (fun p : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) × ℝ≥0∞ =>
      p.1 p.2.toNNReal) := by
    simpa only [normalizedPrefixCurve_endPoint, Function.comp_def] using
      CurveSpace.continuous_endPoint.measurable.comp measurable_normalizedPrefixCurve_toNNReal
  have hend : Measurable (fun p : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) × ℝ≥0∞ =>
      Complex.orthonormalBasisOneI.repr.symm (p.1 p.2.toNNReal)) :=
    Complex.orthonormalBasisOneI.repr.symm.continuous.measurable.comp heval
  rw [Measure.map_map (by fun_prop) hend,
    Measure.map_map Complex.orthonormalBasisOneI.repr.symm.continuous.measurable
      (affinePlaneNormalization c a).continuous.measurable,
    Measure.map_map (by fun_prop) heval]
  congr 1
  funext p
  simp [affinePlaneNormalization, Function.comp_def]

/-- Frontier distance is controlled by the normalized prefix laws associated
with two path-clock measures whose complex endpoints lie on the frontier. -/
theorem levyProkhorovEDist_parentFrontier_le_pathClockCurves
    (μ ν : Measure (C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) × ℝ≥0∞))
    (c : ℂ) {a : ℝ} (ha : 0 < a)
    (hμ : ∀ᵐ z ∂μ.map (fun p => Complex.orthonormalBasisOneI.repr.symm
      (p.1 p.2.toNNReal)), z ∈ frontier (ParentBlock.parentBlock c a))
    (hν : ∀ᵐ z ∂ν.map (fun p => Complex.orthonormalBasisOneI.repr.symm
      (p.1 p.2.toNNReal)), z ∈ frontier (ParentBlock.parentBlock c a)) :
    let endpoint := fun p : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) × ℝ≥0∞ =>
      Complex.orthonormalBasisOneI.repr.symm (p.1 p.2.toNNReal)
    let curve := fun p : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) × ℝ≥0∞ =>
      normalizedPrefixCurve ((affinePlaneNormalization c a).comp p.1) p.2.toNNReal
    letI : MetricSpace MetricPlane := normalizedPlaneMetric c a ha.ne'
    let S : Set MetricPlane := MetricPlane.down ⁻¹' frontier (ParentBlock.parentBlock c a)
    levyProkhorovEDist (((μ.map endpoint).map MetricPlane.up).comap ((↑) : S → MetricPlane))
      (((ν.map endpoint).map MetricPlane.up).comap ((↑) : S → MetricPlane)) ≤
      levyProkhorovEDist (μ.map curve) (ν.map curve) := by
  exact levyProkhorovEDist_parentFrontier_le_curve _ _ _ _ c ha hμ hν
    (map_affine_pathClock_endpoint μ c a) (map_affine_pathClock_endpoint ν c a)

end LatticeProb
end
