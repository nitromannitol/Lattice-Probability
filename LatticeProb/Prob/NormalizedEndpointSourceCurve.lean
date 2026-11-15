import LatticeProb.Prob.SourceCurveParentFrontier
import LatticeProb.Prob.ParentFrontierProkhorov

/-! # Normalized endpoint and finite-curve distances -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set BouRabeeGwynne ReflectedGMS.GMS
open scoped NNReal ENNReal

namespace LatticeProb

/-- For endpoint laws supported on a parent-block frontier, their normalized
ambient distance is bounded by the distance between normalized prefix laws. -/
theorem levyProkhorovEDist_normalizedEndpoint_le_sourcePathClockCurves
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
    levyProkhorovEDist ((μ.map endpoint).map (fun z : ℂ => (z - c) / (a : ℂ)))
      ((ν.map endpoint).map (fun z : ℂ => (z - c) / (a : ℂ))) ≤
      levyProkhorovEDist (μ.map curve) (ν.map curve) := by
  have heq := levyProkhorovEDist_parentFrontier _ _ c ha hμ hν
  have hle := levyProkhorovEDist_parentFrontier_le_sourcePathClockCurves μ ν c ha hμ hν
  exact heq.symm.le.trans hle

end LatticeProb
end
