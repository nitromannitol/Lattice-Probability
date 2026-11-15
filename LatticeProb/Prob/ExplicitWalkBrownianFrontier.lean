import LatticeProb.Prob.ConstantStepSourceFrontier
import LatticeProb.Prob.BrownianStoppedPathClock

/-! # Explicit exit laws on parent frontiers -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigWalk

open CellConfigCappedSquare CellConfigInterpolation

/-- The parent-frontier distance between the walk exit-position law and the
stopped Brownian endpoint law is controlled by the source-curve distance. -/
theorem levyProkhorovEDist_explicit_parentFrontier_le_constantStep
    {H : CellConfig} [Countable H.cells] (hrec : H.Recurrent)
    (hpos : ∀ K, 0 < H.holding K) {K₀ : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K₀ Q)
    (p : H.cells → Plane) {ε m : ℝ≥0} (hε : 0 < ε) (hm : 0 < m)
    (c : ℂ) {a : ℝ} (ha : 0 < a)
    (hstart : planeCoord.symm ((ε : ℝ) • p K₀) ∈ ParentBlock.closedSquare c a)
    (hfinite : ∀ᵐ ω ∂Q, continuousExitTime
      (planeCoord.symm ⁻¹' interior (ParentBlock.parentBlock c a)) 0
      (H.interpolatedWalk p ε ω) ≠ ∞)
    (ρ : Measure (BrownianPath 2)) (hρ : IsStandardBrownianLaw ρ) :
    let U := planeCoord.symm ⁻¹' interior (ParentBlock.parentBlock c a)
    let μ := (Q.map (fun ω => (H.interpolatedWalk p ε ω)
      (continuousExitTime U 0 (H.interpolatedWalk p ε ω)).toNNReal)).map planeCoord.symm
    let ν := ((stoppedBrownianLaw U ((ε : ℝ) • p K₀) ρ).map
      BouRabeeGwynne.CurveSpace.endPoint).map planeCoord.symm
    letI : MetricSpace MetricPlane := normalizedPlaneMetric c a ha.ne'
    let S : Set MetricPlane := MetricPlane.down ⁻¹' frontier (ParentBlock.parentBlock c a)
    levyProkhorovEDist ((μ.map MetricPlane.up).comap ((↑) : S → MetricPlane))
      ((ν.map MetricPlane.up).comap ((↑) : S → MetricPlane)) ≤
      ((max 1 (Real.toNNReal a⁻¹) : ℝ≥0) : ℝ≥0∞) *
        levyProkhorovEDist
          (Q.map (fun ω =>
            let g := ConstantStepInterpolation.continuousPlanePath m
              (fun n => (ε : ℝ) • p (ω n))
            CurveSpaceComparison.isometryEquiv 2
              (normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal)))
          (stoppedBrownianLaw U ((ε : ℝ) • p K₀) ρ) := by
  let U := planeCoord.symm ⁻¹' interior (ParentBlock.parentBlock c a)
  have hU : IsOpen U := isOpen_interior.preimage planeCoord.symm.continuous
  have heval : Measurable (fun q : C(ℝ≥0, Plane) × ℝ≥0∞ => q.1 q.2.toNNReal) := by
    simpa only [normalizedPrefixCurve_endPoint, Function.comp_def] using
      LatticeProb.CurveSpace.continuous_endPoint.measurable.comp
        measurable_normalizedPrefixCurve_toNNReal
  have hw : (walkExitPathClockLaw H p ε U Q).map
      (fun q => planeCoord.symm (q.1 q.2.toNNReal)) =
      (Q.map (fun ω => (H.interpolatedWalk p ε ω)
        (continuousExitTime U 0 (H.interpolatedWalk p ε ω)).toNNReal)).map planeCoord.symm := by
    change (walkExitPathClockLaw H p ε U Q).map
      (planeCoord.symm ∘ fun q : C(ℝ≥0, Plane) × ℝ≥0∞ => q.1 q.2.toNNReal) = _
    rw [← Measure.map_map planeCoord.symm.continuous.measurable heval,
      map_walkExitPathClockLaw_endpoint hrec hpos hQ p ε hU]
  have hb : (ρ.map (fun ω => (translatedBrownianPath ((ε : ℝ) • p K₀) ω,
      BouRabeeGwynne.continuousExitTime U ((ε : ℝ) • p K₀) ω))).map
      (fun q => planeCoord.symm (q.1 q.2.toNNReal)) =
      ((stoppedBrownianLaw U ((ε : ℝ) • p K₀) ρ).map
        BouRabeeGwynne.CurveSpace.endPoint).map planeCoord.symm := by
    change (ρ.map (fun ω => (translatedBrownianPath ((ε : ℝ) • p K₀) ω,
      BouRabeeGwynne.continuousExitTime U ((ε : ℝ) • p K₀) ω))).map
      (planeCoord.symm ∘ fun q : C(ℝ≥0, Plane) × ℝ≥0∞ => q.1 q.2.toNNReal) = _
    rw [← Measure.map_map planeCoord.symm.continuous.measurable heval,
      map_brownian_pathClock_endpoint hU]
  change (ρ.map (fun ω => (translatedBrownianPath ((ε : ℝ) • p K₀) ω,
      LatticeProb.continuousExitTime U ((ε : ℝ) • p K₀) ω))).map
      (fun q => planeCoord.symm (q.1 q.2.toNNReal)) = _ at hb
  have h := levyProkhorovEDist_walk_brownian_parentFrontier_le_constantStep
    hrec hpos hQ p hε hm c ha hstart hfinite ρ hρ
  dsimp only at h ⊢
  rw [hw, hb] at h
  exact h

end LatticeProb.CellConfigWalk
end
