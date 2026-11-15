import LatticeProb.Prob.CellConfigWalkExitMeasurable
import LatticeProb.Prob.DyadicCellConfig

/-! # Frontier support of an interpolated cell-walk exit law -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigWalk

open ReflectedGMS ReflectedGMS.GMS CellConfigCappedSquare

/-- The complex-coordinate law of a finite interpolated-walk exit from the
interior of a set is supported on the frontier of that set. -/
theorem ae_map_interpolatedWalk_exitPosition_mem_frontier
    {H : CellConfig} [Countable H.cells] (hrec : H.Recurrent)
    (hpos : ∀ K, 0 < H.holding K) {K₀ : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K₀ Q)
    (p : H.cells → Plane) (ε : ℝ≥0) (S : Set ℂ)
    (hstart : ∀ᵐ ω ∂Q, (H.interpolatedWalk p ε ω) 0 ∈
      planeCoord.symm ⁻¹' interior S)
    (hfinite : ∀ᵐ ω ∂Q, continuousExitTime (planeCoord.symm ⁻¹' interior S) 0
      (H.interpolatedWalk p ε ω) ≠ ∞) :
    ∀ᵐ z ∂Q.map (fun ω => planeCoord.symm ((H.interpolatedWalk p ε ω)
      (continuousExitTime (planeCoord.symm ⁻¹' interior S) 0
        (H.interpolatedWalk p ε ω)).toNNReal)), z ∈ frontier S := by
  let U : Set Plane := planeCoord.symm ⁻¹' interior S
  have hU : IsOpen U := isOpen_interior.preimage planeCoord.symm.continuous
  have hm := aemeasurable_interpolatedWalk_exitPosition hrec hpos hQ p ε hU
  apply (ae_map_iff (planeCoord.symm.continuous.measurable.comp_aemeasurable hm)
    isClosed_frontier.measurableSet).2
  filter_upwards [hstart, hfinite] with ω hs hf
  have hb : (H.interpolatedWalk p ε ω)
      (continuousExitTime U 0 (H.interpolatedWalk p ε ω)).toNNReal ∈ frontier U := by
    simpa only [zero_add] using
      (continuousExitTime_mem_frontier hU (by simpa only [zero_add] using hs) hf)
  have hc : planeCoord.symm ((H.interpolatedWalk p ε ω)
      (continuousExitTime U 0 (H.interpolatedWalk p ε ω)).toNNReal) ∈
      frontier (interior S) := by
    change _ ∈ planeCoord.symm ⁻¹' frontier (interior S)
    have heq : (planeCoord.symm ⁻¹' frontier (interior S) : Set Plane) = frontier U :=
      planeCoord.symm.toHomeomorph.preimage_frontier (interior S)
    rwa [heq]
  exact frontier_interior_subset hc

end LatticeProb.CellConfigWalk
