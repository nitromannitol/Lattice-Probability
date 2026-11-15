import LatticeProb.Prob.WalkBrownianSourceFrontier
import LatticeProb.Prob.SpatialPrefixCurveLaw

/-! # Spatial normalization and parent-frontier laws -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open scoped NNReal ENNReal

namespace LatticeProb

/-- Affine normalization by a positive side length has the inverse side length
as a Lipschitz constant. -/
theorem affinePlaneNormalization_lipschitz (c : ℂ) {a : ℝ} (ha : 0 < a) :
    LipschitzWith (Real.toNNReal a⁻¹) (affinePlaneNormalization c a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := normalizedPlaneMetric_dist c ha
    (MetricPlane.up (Complex.orthonormalBasisOneI.repr.symm x))
    (MetricPlane.up (Complex.orthonormalBasisOneI.repr.symm y))
  change dist ((Complex.orthonormalBasisOneI.repr.symm x - c) / (a : ℂ))
    ((Complex.orthonormalBasisOneI.repr.symm y - c) / (a : ℂ)) = _ at h
  dsimp only [MetricPlane.up] at h
  change dist (Complex.orthonormalBasisOneI.repr
      ((Complex.orthonormalBasisOneI.repr.symm x - c) / (a : ℂ)))
    (Complex.orthonormalBasisOneI.repr
      ((Complex.orthonormalBasisOneI.repr.symm y - c) / (a : ℂ))) ≤ _
  rw [Complex.orthonormalBasisOneI.repr.isometry.dist_eq, h,
    Complex.orthonormalBasisOneI.repr.symm.isometry.dist_eq]
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr ha.le)]

namespace CellConfigWalk

open CellConfigCappedSquare CellConfigInterpolation

/-- The frontier distance is controlled by the unnormalized source-prefix
distance, with the probability error retained by the factor `max 1 (1 / a)`. -/
theorem levyProkhorovEDist_walk_brownian_parentFrontier_le_unscaled_sourcePrefix
    {H : CellConfig} [Countable H.cells] (hrec : H.Recurrent)
    (hpos : ∀ K, 0 < H.holding K) {K₀ : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K₀ Q)
    (p : H.cells → Plane) {ε : ℝ≥0} (hε : 0 < ε) (c : ℂ) {a : ℝ} (ha : 0 < a)
    (hstart : planeCoord.symm ((ε : ℝ) • p K₀) ∈ ParentBlock.closedSquare c a)
    (hfinite : ∀ᵐ ω ∂Q, continuousExitTime
      (planeCoord.symm ⁻¹' interior (ParentBlock.parentBlock c a)) 0
      (H.interpolatedWalk p ε ω) ≠ ∞)
    (ρ : Measure (BrownianPath 2)) (hρ : IsStandardBrownianLaw ρ) :
    let U := planeCoord.symm ⁻¹' interior (ParentBlock.parentBlock c a)
    let μ := walkExitPathClockLaw H p ε U Q
    let ν := ρ.map (fun ω => (translatedBrownianPath ((ε : ℝ) • p K₀) ω,
      BouRabeeGwynne.continuousExitTime U ((ε : ℝ) • p K₀) ω))
    let endpoint := fun q : C(ℝ≥0, Plane) × ℝ≥0∞ => planeCoord.symm (q.1 q.2.toNNReal)
    let curve := fun q : C(ℝ≥0, Plane) × ℝ≥0∞ =>
      CurveSpaceComparison.isometryEquiv 2 (normalizedPrefixCurve q.1 q.2.toNNReal)
    letI : MetricSpace MetricPlane := normalizedPlaneMetric c a ha.ne'
    let S : Set MetricPlane := MetricPlane.down ⁻¹' frontier (ParentBlock.parentBlock c a)
    levyProkhorovEDist (((μ.map endpoint).map MetricPlane.up).comap ((↑) : S → MetricPlane))
      (((ν.map endpoint).map MetricPlane.up).comap ((↑) : S → MetricPlane)) ≤
      ((max 1 (Real.toNNReal a⁻¹) : ℝ≥0) : ℝ≥0∞) *
        levyProkhorovEDist (μ.map curve) (ν.map curve) := by
  exact (levyProkhorovEDist_walk_brownian_parentFrontier_le_sourcePrefix
    hrec hpos hQ p hε c ha hstart hfinite ρ hρ).trans
      (levyProkhorovEDist_source_spatial_normalizedPrefixCurve_le
        (affinePlaneNormalization c a) (affinePlaneNormalization_lipschitz c ha) _ _)

end CellConfigWalk
end LatticeProb
end
