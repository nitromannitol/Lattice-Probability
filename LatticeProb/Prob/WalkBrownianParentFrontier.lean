import LatticeProb.Prob.ScaledStartExitFrontier
import LatticeProb.Prob.BrownianParentFrontierLaw
import LatticeProb.Prob.ParentFrontierProkhorov

/-! # Normalized distance between parent-block exit laws -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigWalk

open CellConfigCappedSquare CellConfigInterpolation

/-- The frontier distance between the exit laws of a cell walk and Brownian
motion started at the scaled representative equals the distance between their
spatially normalized ambient laws. -/
theorem levyProkhorovEDist_walk_brownian_parentFrontier
    {H : CellConfig} [Countable H.cells] (hrec : H.Recurrent)
    (hpos : ∀ K, 0 < H.holding K) {K₀ : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K₀ Q)
    (p : H.cells → Plane) {ε : ℝ≥0} (hε : 0 < ε) (c : ℂ) {a : ℝ} (ha : 0 < a)
    (hstart : planeCoord.symm ((ε : ℝ) • p K₀) ∈ ParentBlock.closedSquare c a)
    (hfinite : ∀ᵐ ω ∂Q, continuousExitTime
      (planeCoord.symm ⁻¹' interior (ParentBlock.parentBlock c a)) 0
      (H.interpolatedWalk p ε ω) ≠ ∞)
    (ρ : Measure (BrownianPath 2)) (hρ : IsStandardBrownianLaw ρ) :
    let μ := Q.map (fun ω => planeCoord.symm ((H.interpolatedWalk p ε ω)
      (continuousExitTime (planeCoord.symm ⁻¹' interior (ParentBlock.parentBlock c a)) 0
        (H.interpolatedWalk p ε ω)).toNNReal))
    let ν := ((stoppedBrownianLaw
      (planeCoord.symm ⁻¹' interior (ParentBlock.parentBlock c a))
      ((ε : ℝ) • p K₀) ρ).map BouRabeeGwynne.CurveSpace.endPoint).map planeCoord.symm
    letI : MetricSpace MetricPlane := normalizedPlaneMetric c a ha.ne'
    let S : Set MetricPlane := MetricPlane.down ⁻¹' frontier (ParentBlock.parentBlock c a)
    levyProkhorovEDist ((μ.map MetricPlane.up).comap ((↑) : S → MetricPlane))
        ((ν.map MetricPlane.up).comap ((↑) : S → MetricPlane)) =
      levyProkhorovEDist (μ.map (fun z : ℂ => (z - c) / (a : ℂ)))
        (ν.map (fun z : ℂ => (z - c) / (a : ℂ))) := by
  apply levyProkhorovEDist_parentFrontier _ _ c ha
  · exact ae_map_interpolatedWalk_exitPosition_mem_parentFrontier
      hrec hpos hQ p hε c ha hstart hfinite
  · apply ParentBlock.stoppedBrownianLaw_endPoint_complex_ae_mem_frontier c ha.le
    · exact ParentBlock.ball_subset_interior_parentBlock ha.le hstart (Metric.mem_ball_self ha)
    · exact hρ

end LatticeProb.CellConfigWalk
end
