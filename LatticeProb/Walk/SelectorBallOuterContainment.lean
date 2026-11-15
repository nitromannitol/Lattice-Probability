import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.ProperSpace

/-! # Containment of finite selector balls in an outer region -/

set_option autoImplicit false

open Set Metric

namespace LatticeProb

/-- Finite closed balls in an open region admit a uniform tolerance for
pulling their open balls back through two uniformly close position maps. -/
theorem exists_selectorBall_preimage_subset_outer {E V : Type*}
    [MetricSpace E] [ProperSpace E] (centers : Finset E) (r : ℝ)
    {W : Set E} (hW : IsOpen W)
    (hballs : ∀ c ∈ centers, closedBall c r ⊆ W) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p q : V → E),
      (∀ v, dist (p v) (q v) ≤ δ) →
      ∀ c ∈ centers, q ⁻¹' ball c r ⊆ p ⁻¹' W := by
  let K : Set E := ⋃ c ∈ centers, closedBall c r
  have hK : IsCompact K := centers.isCompact_biUnion fun _ _ => isCompact_closedBall _ _
  have hKW : K ⊆ W := by
    intro x hx
    rcases mem_iUnion₂.mp hx with ⟨c, hc, hx⟩
    exact hballs c hc hx
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_cthickening_subset_open hW hKW
  refine ⟨δ, hδ, ?_⟩
  intro p q hp c hc v hv
  apply hδW
  apply mem_cthickening_of_dist_le (p v) (q v) δ K
  · exact mem_iUnion₂.mpr ⟨c, hc, ball_subset_closedBall hv⟩
  · exact hp v

end LatticeProb
