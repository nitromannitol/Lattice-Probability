import LatticeProb.Prob.CellWalkExitFrontier
import LatticeProb.Walk.CellConfigFiniteExit
import LatticeProb.Euclidean.ParentBlockSeparation

/-! # Exit laws from a scaled initial cell representative -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigWalk

open CellConfigCappedSquare CellConfigInterpolation

/-- A finite exit from the interior has frontier support when the scaled
representative of the initial cell lies in the interior. -/
theorem ae_map_interpolatedWalk_exitPosition_mem_frontier_of_scaled_start
    {H : CellConfig} [Countable H.cells] (hrec : H.Recurrent)
    (hpos : ∀ K, 0 < H.holding K) {K₀ : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K₀ Q)
    (p : H.cells → Plane) {ε : ℝ≥0} (hε : 0 < ε) (S : Set ℂ)
    (hstart : planeCoord.symm ((ε : ℝ) • p K₀) ∈ interior S)
    (hfinite : ∀ᵐ ω ∂Q, continuousExitTime (planeCoord.symm ⁻¹' interior S) 0
      (H.interpolatedWalk p ε ω) ≠ ∞) :
    ∀ᵐ z ∂Q.map (fun ω => planeCoord.symm ((H.interpolatedWalk p ε ω)
      (continuousExitTime (planeCoord.symm ⁻¹' interior S) 0
        (H.interpolatedWalk p ε ω)).toNNReal)), z ∈ frontier S := by
  apply ae_map_interpolatedWalk_exitPosition_mem_frontier hrec hpos hQ p ε S _ hfinite
  have hzero : ∀ᵐ ω ∂Q, ω 0 = K₀ := by
    let : IsProbabilityMeasure Q := hQ.1
    apply (mem_ae_iff_prob_eq_one ((measurableSet_singleton K₀).preimage
      (measurable_pi_apply 0))).2
    have heq : {ω : ℕ → H.cells | ω 0 = K₀} =
        {ω | ∀ i : Fin 1, ω i = (fun _ => K₀) i} := by
      ext ω
      constructor
      · intro h i
        fin_cases i
        exact h
      · intro h
        exact h 0
    change Q {ω : ℕ → H.cells | ω 0 = K₀} = 1
    rw [heq, hQ.2 0 (fun _ => K₀)]
    simp
  filter_upwards [hzero, ae_jumpTimesUnbounded_of_recurrent hrec hpos hQ] with ω hz hu
  have ht : (⟨(ε : ℝ) ^ 2 * H.jumpTime ω 0,
      mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos 0)⟩ : ℝ≥0) = 0 := by
    apply Subtype.ext
    simp [CellConfig.jumpTime]
  have hk := interpolatedWalk_at_jumpTime H p ω hpos hu 0 hε
  rw [ht, hz] at hk
  change planeCoord.symm (H.interpolatedWalk p ε ω 0) ∈ interior S
  exact congrArg planeCoord.symm hk ▸ hstart

/-- A scaled representative in a positive square starts inside its parent block,
so finite exit from the parent-block interior lands on the parent frontier. -/
theorem ae_map_interpolatedWalk_exitPosition_mem_parentFrontier
    {H : CellConfig} [Countable H.cells] (hrec : H.Recurrent)
    (hpos : ∀ K, 0 < H.holding K) {K₀ : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K₀ Q)
    (p : H.cells → Plane) {ε : ℝ≥0} (hε : 0 < ε) (c : ℂ) {s : ℝ} (hs : 0 < s)
    (hstart : planeCoord.symm ((ε : ℝ) • p K₀) ∈ ParentBlock.closedSquare c s)
    (hfinite : ∀ᵐ ω ∂Q, continuousExitTime
      (planeCoord.symm ⁻¹' interior (ParentBlock.parentBlock c s)) 0
      (H.interpolatedWalk p ε ω) ≠ ∞) :
    ∀ᵐ z ∂Q.map (fun ω => planeCoord.symm ((H.interpolatedWalk p ε ω)
      (continuousExitTime (planeCoord.symm ⁻¹' interior (ParentBlock.parentBlock c s)) 0
        (H.interpolatedWalk p ε ω)).toNNReal)),
      z ∈ frontier (ParentBlock.parentBlock c s) := by
  apply ae_map_interpolatedWalk_exitPosition_mem_frontier_of_scaled_start
    hrec hpos hQ p hε (ParentBlock.parentBlock c s) _ hfinite
  exact ParentBlock.ball_subset_interior_parentBlock hs.le hstart (Metric.mem_ball_self hs)

end LatticeProb.CellConfigWalk
end
