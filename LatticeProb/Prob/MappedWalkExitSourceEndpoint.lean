import LatticeProb.Prob.MappedConstantStepSourceEndpoint
import LatticeProb.Prob.BrownianStoppedPathClock

/-! # Spatial images of walk exit positions -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigWalk

open CellConfigInterpolation

/-- The distance between spatial images of the walk exit-position law and the
stopped-curve endpoint law is controlled by the source-curve distance. Infinite
clocks are evaluated at zero. -/
theorem levyProkhorovEDist_mapped_exitPositions_le_constantStep_sourceCurves
    {H : CellConfig} [Countable H.cells] (hrec : H.Recurrent)
    (hpos : ∀ K, 0 < H.holding K) {K₀ : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K₀ Q)
    (p : H.cells → Plane) {ε m : ℝ≥0} (hε : 0 < ε) (hm : 0 < m)
    {U : Set Plane} (hU : IsOpen U)
    (hfinite : ∀ᵐ ω ∂Q, continuousExitTime U 0 (H.interpolatedWalk p ε ω) ≠ ∞)
    (z : Plane) (ρ : Measure (BrownianPath 2))
    {Y : Type*} [PseudoEMetricSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {K : ℝ≥0} {f : Plane → Y} (hf : LipschitzWith K f) (hfm : Measurable f) :
    levyProkhorovEDist
      ((Q.map (fun ω => (H.interpolatedWalk p ε ω)
        (continuousExitTime U 0 (H.interpolatedWalk p ε ω)).toNNReal)).map f)
      (((stoppedBrownianLaw U z ρ).map BouRabeeGwynne.CurveSpace.endPoint).map f) ≤
    ((max 1 K : ℝ≥0) : ℝ≥0∞) * levyProkhorovEDist
      (Q.map (fun ω =>
        let g := ConstantStepInterpolation.continuousPlanePath m
          (fun n => (ε : ℝ) • p (ω n))
        CurveSpaceComparison.isometryEquiv 2
          (normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal)))
      (stoppedBrownianLaw U z ρ) := by
  have h := levyProkhorovEDist_mapped_endpoints_le_constantStep_sourceCurves
    hrec hpos hQ p hε hm hU hfinite z ρ hf hfm
  dsimp only at h
  rw [map_walkExitPathClockLaw_endpoint hrec hpos hQ p ε hU,
    map_brownian_pathClock_endpoint hU z ρ] at h
  exact h

end LatticeProb.CellConfigWalk
end
