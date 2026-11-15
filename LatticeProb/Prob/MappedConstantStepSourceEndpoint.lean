import LatticeProb.Prob.ConstantStepSourceEndpoint
import LatticeProb.Prob.LevyProkhorovLipschitz

/-! # Spatial images of constant-step exit endpoints -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigWalk

open CellConfigInterpolation

/-- A Lipschitz spatial image of the exit endpoints is controlled by the
constant-step source-curve distance. Infinite clocks are evaluated at zero. -/
theorem levyProkhorovEDist_mapped_endpoints_le_constantStep_sourceCurves
    {H : CellConfig} [Countable H.cells] (hrec : H.Recurrent)
    (hpos : ∀ K, 0 < H.holding K) {K₀ : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K₀ Q)
    (p : H.cells → Plane) {ε m : ℝ≥0} (hε : 0 < ε) (hm : 0 < m)
    {U : Set Plane} (hU : IsOpen U)
    (hfinite : ∀ᵐ ω ∂Q, continuousExitTime U 0 (H.interpolatedWalk p ε ω) ≠ ∞)
    (z : Plane) (ρ : Measure (BrownianPath 2))
    {Y : Type*} [PseudoEMetricSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {K : ℝ≥0} {f : Plane → Y} (hf : LipschitzWith K f) (hfm : Measurable f) :
    let μ := walkExitPathClockLaw H p ε U Q
    let ν := ρ.map (fun ω => (translatedBrownianPath z ω, BouRabeeGwynne.continuousExitTime U z ω))
    levyProkhorovEDist ((μ.map (fun q => q.1 q.2.toNNReal)).map f)
      ((ν.map (fun q => q.1 q.2.toNNReal)).map f) ≤
    ((max 1 K : ℝ≥0) : ℝ≥0∞) * levyProkhorovEDist
      (Q.map (fun ω =>
        let g := ConstantStepInterpolation.continuousPlanePath m
          (fun n => (ε : ℝ) • p (ω n))
        CurveSpaceComparison.isometryEquiv 2
          (normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal)))
      (stoppedBrownianLaw U z ρ) := by
  exact (levyProkhorovEDist_map_le_of_lipschitz (le_max_left 1 K)
    (hf.weaken (le_max_right 1 K)) hfm _ _).trans
      (by
        simpa only [mul_comm] using
          (mul_le_mul_left (levyProkhorovEDist_endpoints_le_constantStep_sourceCurves
            hrec hpos hQ p hε hm hU hfinite z ρ) ((max 1 K : ℝ≥0) : ℝ≥0∞)))

end LatticeProb.CellConfigWalk
end
