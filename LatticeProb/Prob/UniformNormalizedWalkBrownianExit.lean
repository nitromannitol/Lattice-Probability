import LatticeProb.Prob.NormalizedWalkBrownianExit

/-! # Uniform normalized walk and Brownian exit-law comparison -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigWalk

open CellConfigCappedSquare CellConfigInterpolation

/-- A uniform bound for the stopped-curve distances controls the supremum of
normalized exit-law distances over the same starting cells. -/
theorem iSup_normalized_exit_le_of_constantStep_bound
    {H : CellConfig} [Countable H.cells] (hrec : H.Recurrent)
    (hpos : ∀ K, 0 < H.holding K) {ι : Type*}
    (K : ι → H.cells) (Q : ι → Measure (ℕ → H.cells))
    (hQ : ∀ i, H.IsSRWLaw (K i) (Q i))
    (p : H.cells → Plane) {ε m : ℝ≥0} (hε : 0 < ε) (hm : 0 < m)
    (c : ℂ) {a : ℝ} (ha : 0 < a)
    (hstart : ∀ i, planeCoord.symm ((ε : ℝ) • p (K i)) ∈ ParentBlock.closedSquare c a)
    (hfinite : ∀ i, ∀ᵐ ω ∂Q i, continuousExitTime
      (planeCoord.symm ⁻¹' interior (ParentBlock.parentBlock c a)) 0
      (H.interpolatedWalk p ε ω) ≠ ∞)
    (ρ : Measure (BrownianPath 2)) (hρ : IsStandardBrownianLaw ρ) (B : ℝ≥0∞)
    (hcurve : ∀ i, levyProkhorovEDist
      ((Q i).map (fun ω =>
        let g := ConstantStepInterpolation.continuousPlanePath m
          (fun n => (ε : ℝ) • p (ω n))
        CurveSpaceComparison.isometryEquiv 2
          (normalizedPrefixCurve g (continuousExitTime
            (planeCoord.symm ⁻¹' interior (ParentBlock.parentBlock c a)) 0 g).toNNReal)))
      (stoppedBrownianLaw (planeCoord.symm ⁻¹' interior (ParentBlock.parentBlock c a))
        ((ε : ℝ) • p (K i)) ρ) ≤ B) :
    let U := planeCoord.symm ⁻¹' interior (ParentBlock.parentBlock c a)
    ⨆ i, levyProkhorovEDist
      ((((Q i).map (fun ω => (H.interpolatedWalk p ε ω)
        (continuousExitTime U 0 (H.interpolatedWalk p ε ω)).toNNReal)).map
        planeCoord.symm).map (fun z : ℂ => (z - c) / (a : ℂ)))
      ((((stoppedBrownianLaw U ((ε : ℝ) • p (K i)) ρ).map
        BouRabeeGwynne.CurveSpace.endPoint).map planeCoord.symm).map
        (fun z : ℂ => (z - c) / (a : ℂ))) ≤
      ((max 1 (Real.toNNReal a⁻¹) : ℝ≥0) : ℝ≥0∞) * B := by
  apply iSup_le
  intro i
  have h := levyProkhorovEDist_normalized_exit_le_constantStep
    hrec hpos (hQ i) p hε hm c ha (hstart i) (hfinite i) ρ hρ
  dsimp only at h ⊢
  exact h.trans (mul_le_mul_right (hcurve i) _)

end LatticeProb.CellConfigWalk
end
