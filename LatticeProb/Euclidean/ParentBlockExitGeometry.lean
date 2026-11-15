import LatticeProb.Euclidean.ParentBlockSeparation

/-! # Compact parent blocks and exit balls -/

set_option autoImplicit false

open Set Metric

namespace LatticeProb.ParentBlock

/-- A closed square in the plane is compact. -/
theorem isCompact_closedSquare (c : ℂ) (s : ℝ) : IsCompact (closedSquare c s) := by
  apply ((isCompact_Icc : IsCompact (Icc (c.re - s / 2) (c.re + s / 2))).reProdIm
    (isCompact_Icc : IsCompact (Icc (c.im - s / 2) (c.im + s / 2)))).of_isClosed_subset (isClosed_closedSquare c s)
  intro z hz
  change |z.re - c.re| ≤ s / 2 ∧ |z.im - c.im| ≤ s / 2 at hz
  change z.re ∈ Icc _ _ ∧ z.im ∈ Icc _ _
  obtain ⟨h1, h2⟩ := abs_le.mp hz.1
  obtain ⟨h3, h4⟩ := abs_le.mp hz.2
  constructor <;> constructor <;> linarith

/-- A parent block is compact in Euclidean coordinates. -/
theorem isCompact_parentBlock_preimage (c : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    IsCompact (Complex.orthonormalBasisOneI.repr.symm ⁻¹' parentBlock c s) := by
  rw [parentBlock_eq hs]
  exact Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.isCompact_preimage.mpr
    (isCompact_closedSquare c (3 * s))

/-- A closed ball centered in the inner square and of radius at most its side
is contained in the parent block. -/
theorem closedBall_subset_parentBlock {c x : ℂ} {s r : ℝ}
    (hs : 0 ≤ s) (hr : r ≤ s) (hx : x ∈ closedSquare c s) :
    closedBall x r ⊆ parentBlock c s := by
  intro y hy
  rw [parentBlock_eq hs]
  change |y.re - c.re| ≤ 3 * s / 2 ∧ |y.im - c.im| ≤ 3 * s / 2
  have hnorm : ‖y - x‖ ≤ s := by
    simpa only [dist_eq_norm] using (show dist y x ≤ r from hy).trans hr
  have hre : |y.re - x.re| ≤ s := by
    simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (y - x)).trans hnorm
  have him : |y.im - x.im| ≤ s := by
    simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (y - x)).trans hnorm
  change |x.re - c.re| ≤ s / 2 ∧ |x.im - c.im| ≤ s / 2 at hx
  constructor
  · calc
      |y.re - c.re| = |(y.re - x.re) + (x.re - c.re)| := by congr 1; ring
      _ ≤ |y.re - x.re| + |x.re - c.re| := abs_add_le _ _
      _ ≤ 3 * s / 2 := by linarith [hx.1]
  · calc
      |y.im - c.im| = |(y.im - x.im) + (x.im - c.im)| := by congr 1; ring
      _ ≤ |y.im - x.im| + |x.im - c.im| := abs_add_le _ _
      _ ≤ 3 * s / 2 := by linarith [hx.2]

/-- Frontiers of such exit balls lie in the same compact parent block. -/
theorem frontier_ball_subset_parentBlock_preimage
    {c : ℂ} {x : EuclideanSpace ℝ (Fin 2)} {s r : ℝ}
    (hs : 0 ≤ s) (hr : r ≤ s)
    (hx : Complex.orthonormalBasisOneI.repr.symm x ∈ closedSquare c s) :
    frontier (ball x r) ⊆
      Complex.orthonormalBasisOneI.repr.symm ⁻¹' parentBlock c s := by
  intro y hy
  have hy' : y ∈ closedBall x r :=
    closure_ball_subset_closedBall (frontier_subset_closure hy)
  apply closedBall_subset_parentBlock hs hr hx
  change dist (Complex.orthonormalBasisOneI.repr.symm y)
    (Complex.orthonormalBasisOneI.repr.symm x) ≤ r
  simpa only [Complex.orthonormalBasisOneI.repr.symm.isometry.dist_eq] using (show dist y x ≤ r from hy')

end LatticeProb.ParentBlock
