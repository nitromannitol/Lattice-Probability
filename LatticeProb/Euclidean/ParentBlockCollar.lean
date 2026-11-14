import LatticeProb.Euclidean.ParentBlock

/-! # Oscillation inside a parent-block collar -/

set_option autoImplicit false

noncomputable section

open Set

namespace LatticeProb.ParentBlock

/-- A collar of the parent block increases the distance bound from a point in
its child square by at most the collar radius. -/
theorem dist_le_of_mem_cthickening_parentBlock {c x y : ℂ} {s r : ℝ}
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hx : x ∈ closedSquare c s)
    (hy : y ∈ Metric.cthickening r (parentBlock c s)) :
    dist y x ≤ r + 2 * Real.sqrt 2 * s := by
  have hc : IsClosed (parentBlock c s) := by
    rw [parentBlock_eq hs]
    exact isClosed_closedSquare c (3 * s)
  rw [hc.cthickening_eq_biUnion_closedBall hr] at hy
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp hy
  have hzx : dist z x ≤ 2 * Real.sqrt 2 * s := by
    simpa [dist_eq_norm] using norm_sub_le_of_mem_of_mem_parentBlock hs hx hz
  exact (dist_triangle y z x).trans (add_le_add hyz hzx)

/-- The same bound applies to a collar of any subset of the parent block. -/
theorem dist_le_of_mem_cthickening_subset_parentBlock {c x y : ℂ} {s r : ℝ}
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hx : x ∈ closedSquare c s)
    {U : Set ℂ} (hU : U ⊆ parentBlock c s)
    (hy : y ∈ Metric.cthickening r U) :
    dist y x ≤ r + 4 * s := by
  have h := dist_le_of_mem_cthickening_parentBlock hs hr hx
    (Metric.cthickening_subset_of_subset r hU hy)
  have htwo : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hbound : 2 * Real.sqrt 2 * s ≤ 4 * s := by nlinarith
  linarith

end LatticeProb.ParentBlock
end
