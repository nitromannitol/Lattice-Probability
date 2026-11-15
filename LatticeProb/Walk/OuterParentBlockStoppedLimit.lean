import LatticeProb.Euclidean.ParentBlockSeparation
import LatticeProb.Walk.FixedBufferStoppedBallLimit

/-! # Stopped path limits with an outer parent-block endpoint -/

set_option autoImplicit false

open Filter Set Metric
open scoped NNReal ENNReal Topology

namespace LatticeProb.UnboundedRayIntervalIntegrand

/-- An endpoint outside an outer parent block supplies a fixed buffer for
convergence of paths stopped on a smaller ball. -/
theorem eventually_dist_stopped_ball_lt_of_outside_parentBlock
    {α : Type*} {l : Filter α}
    (F G : α → Path 2) (T U : α → ℝ≥0) (φ ψ : α → ℝ≥0 ≃o ℝ≥0)
    (e : α → ℝ) (R δ S : ℝ) (g : Path 2)
    (hG : Tendsto (fun i => (G i).comp ⟨ψ i, (ψ i).continuous⟩) l (𝓝 g))
    (he : Tendsto e l (𝓝 0))
    (hunb : ¬ Bornology.IsBounded (Set.range g))
    (hc : ContinuousAt (fun r : ℝ => ballClock g r) R)
    (hclose : ∀ᶠ i in l, ∀ t, dist (F i (min t (T i)))
      (G i (min (φ i t) (U i))) ≤ e i)
    (hδ : 0 < δ) (hS : 0 < S) (hRS : R + δ ≤ S)
    (hterminal : ∀ᶠ i in l,
      Complex.orthonormalBasisOneI.repr.symm (G i (U i)) ∉ ParentBlock.parentBlock 0 S)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ t : ℝ≥0,
      dist (F i (min t (ballClock (F i) R).toNNReal))
        (G i (min (φ i t) (ballClock (G i) R).toNNReal)) < ε := by
  apply eventually_dist_stopped_ball_lt_of_fixed_buffer F G T U φ ψ e R δ g
    hG he hunb hc hclose hδ ?_ hε
  have hcenter : (0 : ℂ) ∈ ParentBlock.closedSquare 0 S := by
    simp only [ParentBlock.closedSquare, Set.mem_ofPred_eq, Complex.zero_re, Complex.zero_im,
      sub_self, abs_zero]
    constructor <;> linarith
  filter_upwards [hterminal] with i hi
  intro hb
  apply hi
  apply interior_subset (ParentBlock.ball_subset_interior_parentBlock hS.le hcenter ?_)
  have hb' : dist (G i (U i)) 0 < S := lt_of_lt_of_le hb hRS
  have hd : dist (Complex.orthonormalBasisOneI.repr.symm (G i (U i))) 0 =
      dist (G i (U i)) 0 := by
    simpa only [map_zero] using
      (Complex.orthonormalBasisOneI.repr.symm.isometry.dist_eq (G i (U i)) 0)
  simpa only [Metric.mem_ball, hd] using hb'

end LatticeProb.UnboundedRayIntervalIntegrand
