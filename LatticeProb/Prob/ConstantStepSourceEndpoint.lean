import LatticeProb.Prob.SourcePrefixEndpointDistance
import LatticeProb.Prob.WalkSourcePrefixLaw
import LatticeProb.Prob.BrownianSourcePrefixLaw

/-! # Endpoint distances and constant-step exit curves -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigWalk

open CellConfigInterpolation

/-- The endpoint-law distance is bounded by the source-curve distance for a
constant-step walk and a stopped translated path. Infinite clocks are evaluated
at zero. -/
theorem levyProkhorovEDist_endpoints_le_constantStep_sourceCurves
    {H : CellConfig} [Countable H.cells] (hrec : H.Recurrent)
    (hpos : ∀ K, 0 < H.holding K) {K₀ : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K₀ Q)
    (p : H.cells → Plane) {ε m : ℝ≥0} (hε : 0 < ε) (hm : 0 < m)
    {U : Set Plane} (hU : IsOpen U)
    (hfinite : ∀ᵐ ω ∂Q, continuousExitTime U 0 (H.interpolatedWalk p ε ω) ≠ ∞)
    (z : Plane) (ρ : Measure (BrownianPath 2)) :
    let μ := walkExitPathClockLaw H p ε U Q
    let ν := ρ.map (fun ω => (translatedBrownianPath z ω, BouRabeeGwynne.continuousExitTime U z ω))
    levyProkhorovEDist (μ.map (fun q => q.1 q.2.toNNReal))
      (ν.map (fun q => q.1 q.2.toNNReal)) ≤
    levyProkhorovEDist
      (Q.map (fun ω =>
        let g := ConstantStepInterpolation.continuousPlanePath m
          (fun n => (ε : ℝ) • p (ω n))
        CurveSpaceComparison.isometryEquiv 2
          (normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal)))
      (stoppedBrownianLaw U z ρ) := by
  have h := levyProkhorovEDist_pathClockEndpoints_le_sourcePrefixes
    (walkExitPathClockLaw H p ε U Q)
    (ρ.map (fun ω => (translatedBrownianPath z ω, BouRabeeGwynne.continuousExitTime U z ω)))
  rw [map_walkExitPathClockLaw_sourcePrefix_eq_constantStep hrec hpos hQ p hε hm hU hfinite,
    map_brownian_pathClock_sourcePrefix hU] at h
  exact h

end LatticeProb.CellConfigWalk
end
