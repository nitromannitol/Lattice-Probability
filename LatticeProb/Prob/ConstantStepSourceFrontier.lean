import LatticeProb.Prob.AffineSourceFrontier
import LatticeProb.Prob.WalkSourcePrefixLaw
import LatticeProb.Prob.BrownianSourcePrefixLaw

/-! # Parent-frontier distances and constant-step exit curves -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigWalk

open CellConfigCappedSquare CellConfigInterpolation

/-- Bound the walk and Brownian parent-frontier distance by the source-curve
law distance for the constant-step walk and stopped Brownian motion. -/
theorem levyProkhorovEDist_walk_brownian_parentFrontier_le_constantStep
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
    let μ := walkExitPathClockLaw H p ε U Q
    let ν := ρ.map (fun ω => (translatedBrownianPath ((ε : ℝ) • p K₀) ω,
      continuousExitTime U ((ε : ℝ) • p K₀) ω))
    let endpoint := fun q : C(ℝ≥0, Plane) × ℝ≥0∞ => planeCoord.symm (q.1 q.2.toNNReal)
    letI : MetricSpace MetricPlane := normalizedPlaneMetric c a ha.ne'
    let S : Set MetricPlane := MetricPlane.down ⁻¹' frontier (ParentBlock.parentBlock c a)
    levyProkhorovEDist (((μ.map endpoint).map MetricPlane.up).comap ((↑) : S → MetricPlane))
      (((ν.map endpoint).map MetricPlane.up).comap ((↑) : S → MetricPlane)) ≤
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
  have h := levyProkhorovEDist_walk_brownian_parentFrontier_le_unscaled_sourcePrefix
    hrec hpos hQ p hε c ha hstart hfinite ρ hρ
  dsimp only at h ⊢
  rw [map_walkExitPathClockLaw_sourcePrefix_eq_constantStep hrec hpos hQ p hε hm hU hfinite,
    map_brownian_pathClock_sourcePrefix hU] at h
  exact h

end LatticeProb.CellConfigWalk
end
