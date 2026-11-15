import LatticeProb.Prob.WalkBrownianPathClockFrontier
import LatticeProb.Prob.SourceCurveParentFrontier

/-! # Walk and Brownian parent-frontier laws in the source curve space -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigWalk

open CellConfigCappedSquare CellConfigInterpolation

/-- The parent-frontier exit-law distance is bounded by the distance between
normalized walk and Brownian path-prefix laws in the source curve space. -/
theorem levyProkhorovEDist_walk_brownian_parentFrontier_le_sourcePrefix
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
      CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve ((affinePlaneNormalization c a).comp q.1) q.2.toNNReal)
    letI : MetricSpace MetricPlane := normalizedPlaneMetric c a ha.ne'
    let S : Set MetricPlane := MetricPlane.down ⁻¹' frontier (ParentBlock.parentBlock c a)
    levyProkhorovEDist (((μ.map endpoint).map MetricPlane.up).comap ((↑) : S → MetricPlane))
      (((ν.map endpoint).map MetricPlane.up).comap ((↑) : S → MetricPlane)) ≤
      levyProkhorovEDist (μ.map curve) (ν.map curve) := by
  let curve := fun q : C(ℝ≥0, Plane) × ℝ≥0∞ =>
    normalizedPrefixCurve ((affinePlaneNormalization c a).comp q.1) q.2.toNNReal
  have hc : Measurable curve := by
    have hp : Measurable (fun q : C(ℝ≥0, Plane) × ℝ≥0∞ =>
        ((affinePlaneNormalization c a).comp q.1, q.2)) :=
      ((ContinuousMap.continuous_postcomp (affinePlaneNormalization c a)).measurable.comp
        measurable_fst).prodMk measurable_snd
    exact measurable_normalizedPrefixCurve_toNNReal.comp hp
  let e := CurveSpaceComparison.isometryEquiv 2
  have he : MeasurableEmbedding e := e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  let U := planeCoord.symm ⁻¹' interior (ParentBlock.parentBlock c a)
  let μ := walkExitPathClockLaw H p ε U Q
  let ν := ρ.map (fun ω => (translatedBrownianPath ((ε : ℝ) • p K₀) ω,
    BouRabeeGwynne.continuousExitTime U ((ε : ℝ) • p K₀) ω))
  have hd := levyProkhorovEDist_map_eq_of_isometry e.isometry he (μ.map curve) (ν.map curve)
  rw [Measure.map_map he.measurable hc, Measure.map_map he.measurable hc] at hd
  have h := levyProkhorovEDist_walk_brownian_parentFrontier_le_prefix
    hrec hpos hQ p hε c ha hstart hfinite ρ hρ
  exact h.trans_eq hd.symm

end LatticeProb.CellConfigWalk
end
