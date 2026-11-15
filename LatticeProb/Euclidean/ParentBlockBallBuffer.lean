import LatticeProb.Euclidean.ParentBlock

/-! # Ball bounds for parent blocks -/

set_option autoImplicit false

open Set

namespace LatticeProb.ParentBlock

/-- A parent block is contained in a ball around any point near one of its
square's points. -/
theorem parentBlock_subset_ball_of_mem_closedSquare
    {a c x : ℂ} {r s : ℝ} (hs : 0 ≤ s)
    (hx : x ∈ closedSquare c s) (hxa : x ∈ Metric.ball a r) :
    parentBlock c s ⊆ Metric.ball a (r + 4 * s) := by
  intro y hy
  have hyx : dist y x ≤ 4 * s := by
    simpa only [dist_eq_norm] using norm_sub_le_four_mul_of_mem_of_mem_parentBlock hs hx hy
  have hxa' : dist x a < r := hxa
  change dist y a < r + 4 * s
  linarith [dist_triangle y x a]

/-- The closed mesh buffer around every point of a parent block remains in
an outer ball when the anchor, block side and buffer fit inside its radius. -/
theorem closedBall_subset_ball_of_mem_parentBlock
    {a c x y : ℂ} {r R s ρ : ℝ} (hs : 0 ≤ s)
    (hx : x ∈ closedSquare c s) (hxa : x ∈ Metric.ball a r)
    (hy : y ∈ parentBlock c s) (hmargin : r + 4 * s + ρ ≤ R) :
    Metric.closedBall y ρ ⊆ Metric.ball a R := by
  intro z hz
  have hya : dist y a < r + 4 * s :=
    parentBlock_subset_ball_of_mem_closedSquare hs hx hxa hy
  have hzy : dist z y ≤ ρ := hz
  change dist z a < R
  linarith [dist_triangle z y a]

end LatticeProb.ParentBlock
