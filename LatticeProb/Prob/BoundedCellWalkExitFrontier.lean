import LatticeProb.Prob.CellWalkExitFrontier
import LatticeProb.Walk.CellConfigFrontierFiniteExit

/-! # Exit-law support for bounded sets -/

set_option autoImplicit false

open MeasureTheory Set
open ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigWalk

open CellConfigCappedSquare

/-- Frontier hits give finite exit and frontier support for the complex-coordinate
interpolated walk stopped on leaving the interior of a bounded set. -/
theorem ae_map_interpolatedWalk_exitPosition_mem_frontier_of_ball_frontier_hits
    {H : CellConfig} [Countable H.cells] (hH : H.IsCellConfiguration)
    (hrec : H.Recurrent) (hpos : ∀ K, 0 < H.holding K) {K₀ : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K₀ Q)
    (p : H.cells → Plane) (hp : ∀ K, p K ∈ (K.1 : Set Plane))
    {ε : ℝ≥0} (hε : 0 < ε) (S : Set ℂ) (hS : Bornology.IsBounded S)
    (z : Plane)
    (hstart : ∀ᵐ ω ∂Q, (H.interpolatedWalk p ε ω) 0 ∈
      planeCoord.symm ⁻¹' interior S)
    (hhit : ∀ R : ℝ, 0 < R → z ∈ Metric.ball (0 : Plane) R →
      ∀ᵐ ω ∂Q, hitTime {K : H.cells |
        ((K.1 : Set Plane) ∩ frontier (Metric.ball (0 : Plane) R)).Nonempty} ω ≠ ⊤) :
    ∀ᵐ w ∂Q.map (fun ω => planeCoord.symm ((H.interpolatedWalk p ε ω)
      (continuousExitTime (planeCoord.symm ⁻¹' interior S) 0
        (H.interpolatedWalk p ε ω)).toNNReal)), w ∈ frontier S := by
  have hbounded : Bornology.IsBounded (planeCoord.symm ⁻¹' interior S) :=
    (planeCoord.symm.isometry.antilipschitzWith.isBounded_preimage hS).subset
      (preimage_mono interior_subset)
  have hfinite := CellConfigInterpolation.ae_continuousExitTime_ne_top_of_recurrent_ball_frontier_hits
    H hH p hp hpos hrec hε hbounded z hQ hhit
  exact ae_map_interpolatedWalk_exitPosition_mem_frontier hrec hpos hQ p ε S hstart hfinite

end LatticeProb.CellConfigWalk
