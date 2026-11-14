import LatticeProb.Euclidean.ParentBlock

/-!
# Separation of a square from the boundary of its parent block

A point in a square is at least one side length from the complement of the interior of its parent
block. This lower bound complements the oscillation bound inside the block.
-/

set_option autoImplicit false

open Set Metric

namespace LatticeProb.ParentBlock

/-- A ball of radius equal to the side length around any point of the square lies inside the
interior of its parent block. -/
theorem ball_subset_interior_parentBlock {c x : ℂ} {s : ℝ} (hs : 0 ≤ s)
    (hx : x ∈ closedSquare c s) : ball x s ⊆ interior (parentBlock c s) := by
  apply interior_maximal _ isOpen_ball
  intro y hy
  rw [parentBlock_eq hs]
  have hy' : ‖y - x‖ < s := by simpa only [mem_ball, dist_eq_norm] using hy
  have hre : |(y - x).re| < s := lt_of_le_of_lt (Complex.abs_re_le_norm _) hy'
  have him : |(y - x).im| < s := lt_of_le_of_lt (Complex.abs_im_le_norm _) hy'
  change |y.re - c.re| ≤ 3 * s / 2 ∧ |y.im - c.im| ≤ 3 * s / 2
  constructor
  · have h := abs_add_le (y.re - x.re) (x.re - c.re)
    simp only [Complex.sub_re] at hre
    change |x.re - c.re| ≤ s / 2 ∧ |x.im - c.im| ≤ s / 2 at hx
    have he : y.re - c.re = (y.re - x.re) + (x.re - c.re) := by ring
    rw [he]
    linarith [hx.1]
  · have h := abs_add_le (y.im - x.im) (x.im - c.im)
    simp only [Complex.sub_im] at him
    change |x.re - c.re| ≤ s / 2 ∧ |x.im - c.im| ≤ s / 2 at hx
    have he : y.im - c.im = (y.im - x.im) + (x.im - c.im) := by ring
    rw [he]
    linarith [hx.2]

/-- Exiting the interior of a square's parent block requires displacement at least its side length. -/
theorem side_le_norm_sub_of_not_mem_interior_parentBlock {c x y : ℂ} {s : ℝ} (hs : 0 ≤ s)
    (hx : x ∈ closedSquare c s) (hy : y ∉ interior (parentBlock c s)) : s ≤ ‖y - x‖ := by
  by_contra h
  apply hy
  apply ball_subset_interior_parentBlock hs hx
  simpa only [mem_ball, dist_eq_norm] using (lt_of_not_ge h)

end LatticeProb.ParentBlock
