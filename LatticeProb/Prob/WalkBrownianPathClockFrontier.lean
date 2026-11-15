import LatticeProb.Prob.PathClockParentFrontier
import LatticeProb.Prob.WalkExitPathClockLaw
import LatticeProb.Prob.BrownianStoppedPathClock
import LatticeProb.Prob.WalkBrownianParentFrontier

/-! # Walk and Brownian exit laws from joint path-clock laws -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigWalk

open CellConfigCappedSquare CellConfigInterpolation

/-- The distance between parent-frontier exit laws is bounded by the distance
between the normalized finite-prefix laws of the joint path-clock measures. -/
theorem levyProkhorovEDist_walk_brownian_parentFrontier_le_prefix
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
      normalizedPrefixCurve ((affinePlaneNormalization c a).comp q.1) q.2.toNNReal
    letI : MetricSpace MetricPlane := normalizedPlaneMetric c a ha.ne'
    let S : Set MetricPlane := MetricPlane.down ⁻¹' frontier (ParentBlock.parentBlock c a)
    levyProkhorovEDist (((μ.map endpoint).map MetricPlane.up).comap ((↑) : S → MetricPlane))
      (((ν.map endpoint).map MetricPlane.up).comap ((↑) : S → MetricPlane)) ≤
      levyProkhorovEDist (μ.map curve) (ν.map curve) := by
  let U := planeCoord.symm ⁻¹' interior (ParentBlock.parentBlock c a)
  have hU : IsOpen U := isOpen_interior.preimage planeCoord.symm.continuous
  have heval : Measurable (fun q : C(ℝ≥0, Plane) × ℝ≥0∞ => q.1 q.2.toNNReal) := by
    simpa only [normalizedPrefixCurve_endPoint, Function.comp_def] using
      LatticeProb.CurveSpace.continuous_endPoint.measurable.comp
        measurable_normalizedPrefixCurve_toNNReal
  have hw : (walkExitPathClockLaw H p ε U Q).map
      (fun q => planeCoord.symm (q.1 q.2.toNNReal)) =
      Q.map (fun ω => planeCoord.symm ((H.interpolatedWalk p ε ω)
        (continuousExitTime U 0 (H.interpolatedWalk p ε ω)).toNNReal)) := by
    change (walkExitPathClockLaw H p ε U Q).map
      (planeCoord.symm ∘ fun q : C(ℝ≥0, Plane) × ℝ≥0∞ => q.1 q.2.toNNReal) = _
    rw [← Measure.map_map planeCoord.symm.continuous.measurable heval,
      map_walkExitPathClockLaw_endpoint hrec hpos hQ p ε hU]
    have hpath := aemeasurable_interpolatedWalk_exitPathClock hrec hpos hQ p ε hU
    have hexit := heval.comp_aemeasurable hpath
    exact AEMeasurable.map_map_of_aemeasurable planeCoord.symm.continuous.measurable.aemeasurable hexit
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
  apply levyProkhorovEDist_parentFrontier_le_pathClockCurves _ _ c ha
  · rw [hw]
    exact ae_map_interpolatedWalk_exitPosition_mem_parentFrontier
      hrec hpos hQ p hε c ha hstart hfinite
  · rw [hb]
    apply ParentBlock.stoppedBrownianLaw_endPoint_complex_ae_mem_frontier c ha.le
    · exact ParentBlock.ball_subset_interior_parentBlock ha.le hstart (Metric.mem_ball_self ha)
    · exact hρ

end LatticeProb.CellConfigWalk
end
