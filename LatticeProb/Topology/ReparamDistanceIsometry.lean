import LatticeProb.Topology.StoppedRayIntervalDistance

/-! # Spatial isometries and reparametrization distances -/

set_option autoImplicit false
open scoped ENNReal NNReal

namespace LatticeProb.ReparamDistanceIsometry

variable {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]

/-- Postcomposition by an isometry preserves the distance of rays. -/
theorem reparamEDist_comp_isometry (i : E → F) (hi : Isometry i)
    (f g : ℝ≥0 → E) :
    ReparamEDist.reparamEDist (i ∘ f) (i ∘ g) = ReparamEDist.reparamEDist f g := by
  simp only [ReparamEDist.reparamEDist, Function.comp_apply, hi.edist_eq]

/-- Postcomposition by an isometry preserves the distance of intervals, including infinite ones. -/
theorem intervalEDist_comp_isometry (i : E → F) (hi : Isometry i)
    (f g : ℝ≥0 → E) (T U : ℝ≥0∞) :
    IntervalReparamEDist.intervalEDist (i ∘ f) (i ∘ g) T U =
      IntervalReparamEDist.intervalEDist f g T U := by
  simp only [IntervalReparamEDist.intervalEDist, Function.comp_apply, hi.edist_eq]

/-- Read a continuous complex path in its standard Euclidean coordinates. -/
noncomputable def complexToEuclideanPath (f : C(ℝ≥0, ℂ)) :
    C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) :=
  (⟨Complex.orthonormalBasisOneI.repr, Complex.orthonormalBasisOneI.repr.continuous⟩ :
    C(ℂ, EuclideanSpace ℝ (Fin 2))).comp f

/-- Euclidean coordinates preserve the finite-prefix distance of complex rays. -/
theorem complex_stoppedRay_eq_normalizedPrefixCurve
    (f g : C(ℝ≥0, ℂ)) (T U : ℝ≥0) :
    ReparamEDist.reparamEDist (fun t => f (min t T)) (fun t => g (min t U)) =
      edist (normalizedPrefixCurve (complexToEuclideanPath f) T)
        (normalizedPrefixCurve (complexToEuclideanPath g) U) := by
  rw [← StoppedRayIntervalDistance.reparamEDist_stopped_eq_normalizedPrefixCurve
    (complexToEuclideanPath f) (complexToEuclideanPath g) T U]
  exact (reparamEDist_comp_isometry Complex.orthonormalBasisOneI.repr
    Complex.orthonormalBasisOneI.repr.isometry _ _).symm

end LatticeProb.ReparamDistanceIsometry
