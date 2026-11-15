import LatticeProb.Prob.ExplicitWalkBrownianFrontier
import LatticeProb.Prob.WalkBrownianParentFrontier

/-! # Normalized walk and Brownian exit laws -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigWalk

open CellConfigCappedSquare CellConfigInterpolation

/-- The normalized walk and Brownian exit-law distance is bounded by the
constant-step stopped-curve distance. -/
theorem levyProkhorovEDist_normalized_exit_le_constantStep
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
    levyProkhorovEDist (μ.map (fun z : ℂ => (z - c) / (a : ℂ)))
      (ν.map (fun z : ℂ => (z - c) / (a : ℂ))) ≤
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
  have heval := aemeasurable_interpolatedWalk_exitPosition hrec hpos hQ p ε hU
  have hmap := AEMeasurable.map_map_of_aemeasurable
    (planeCoord.symm.continuous.measurable.aemeasurable) heval
  simp only [Function.comp_def] at hmap
  have heq := levyProkhorovEDist_walk_brownian_parentFrontier
    hrec hpos hQ p hε c ha hstart hfinite ρ hρ
  have hbound := levyProkhorovEDist_explicit_parentFrontier_le_constantStep
    hrec hpos hQ p hε hm c ha hstart hfinite ρ hρ
  dsimp only at heq hbound ⊢
  rw [hmap.symm] at heq
  exact heq.symm.le.trans hbound

end LatticeProb.CellConfigWalk
end
