import LatticeProb.Euclidean.GridEdgeRectangle

/-!
# Unions of closed grid squares and their interiors along the grid edges

Fix a mesh `s > 0`. For a set `S ⊆ ℤ²` of indices, `gridSquares s S` is the union of the closed
grid squares `[j s, (j + 1) s] × [m s, (m + 1) s]`, `(j, m) ∈ S` (a grid polygon when `S` is finite).

If `y` and `b` lie on the grid lines, `|y - b| < r ≤ s` and `b` is at distance at least `r` of the
vertices, then `y` and `b` lie on one open edge of the grid (`eq_re_or_eq_im_of_le_infDist`), and

* `mem_gridSquares_iff_of_le_infDist`: `y ∈ gridSquares s S ↔ b ∈ gridSquares s S`;
* `mem_interior_gridSquares_iff_of_le_infDist`: the same holds for the interior.

So a grid polygon and its interior meet each open grid edge either in nothing or in the whole edge.

For the interior, the shift `x ↦ x + (y - b)` along the edge preserves membership in every closed
grid rectangle for `x` near `b` (`add_mem_gridRect_iff_of_im_eq_zero`,
`add_mem_gridRect_iff_of_re_eq_zero`), and a shift with this property near a point preserves
membership in the interior (`add_mem_interior_iff_of_forall_dist_lt`).
-/

open Metric

namespace LatticeProb

namespace GridCells

/-- The union of the closed grid squares `[j s, (j + 1) s] × [m s, (m + 1) s]` over `(j, m) ∈ S`. -/
def gridSquares (s : ℝ) (S : Set (ℤ × ℤ)) : Set ℂ :=
  ⋃ k ∈ S, gridRect s k.1 (k.1 + 1) k.2 (k.2 + 1)

/-- **Interior under a local shift.** If translation by `v` preserves membership in `A` on the
ball of radius `ε > 0` around `b`, then `b + v` is an interior point of `A` if and only if `b` is. -/
theorem add_mem_interior_iff_of_forall_dist_lt {E : Type*} [SeminormedAddCommGroup E] {A : Set E}
    {b v : E} {ε : ℝ} (hε : 0 < ε) (h : ∀ x, dist x b < ε → (x + v ∈ A ↔ x ∈ A)) :
    b + v ∈ interior A ↔ b ∈ interior A := by
  simp only [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  constructor
  · rintro ⟨δ, hδ, hsub⟩
    refine ⟨min δ ε, lt_min hδ hε, fun x hx => ?_⟩
    have hx' : dist x b < min δ ε := hx
    rw [← h x (hx'.trans_le (min_le_right _ _))]
    apply hsub
    change dist (x + v) (b + v) < δ
    rw [dist_add_right]
    exact hx'.trans_le (min_le_left _ _)
  · rintro ⟨δ, hδ, hsub⟩
    refine ⟨min δ ε, lt_min hδ hε, fun x hx => ?_⟩
    have hx' : dist (x - v) b < min δ ε := by
      rw [← dist_add_right (x - v) b v, sub_add_cancel]
      exact hx
    have hmem := (h (x - v) (hx'.trans_le (min_le_right _ _))).2
      (hsub (hx'.trans_le (min_le_left _ _)))
    rwa [sub_add_cancel] at hmem

/-- **Horizontal shifts.** A horizontal shift `v` shorter than the horizontal distance from `x` to
every vertical grid line preserves membership in every closed grid rectangle. -/
theorem add_mem_gridRect_iff_of_im_eq_zero {s : ℝ} {x v : ℂ} (hv : v.im = 0)
    (hfar : ∀ k : ℤ, |v.re| < |x.re - k * s|) (a₁ a₂ c₁ c₂ : ℤ) :
    x + v ∈ gridRect s a₁ a₂ c₁ c₂ ↔ x ∈ gridRect s a₁ a₂ c₁ c₂ := by
  have hd : ∀ k : ℤ, |(x + v).re - x.re| < |x.re - k * s| := fun k => by
    rw [Complex.add_re, add_sub_cancel_left]
    exact hfar k
  change (a₁ : ℝ) * s ≤ (x + v).re ∧ (x + v).re ≤ a₂ * s ∧ (c₁ : ℝ) * s ≤ (x + v).im ∧
      (x + v).im ≤ c₂ * s ↔
    (a₁ : ℝ) * s ≤ x.re ∧ x.re ≤ a₂ * s ∧ (c₁ : ℝ) * s ≤ x.im ∧ x.im ≤ c₂ * s
  rw [le_iff_le_of_le_abs_sub le_rfl (hd a₁), le_iff_le_of_le_abs_sub' le_rfl (hd a₂),
    Complex.add_im, hv, add_zero]

/-- **Vertical shifts.** A vertical shift `v` shorter than the vertical distance from `x` to every
horizontal grid line preserves membership in every closed grid rectangle. -/
theorem add_mem_gridRect_iff_of_re_eq_zero {s : ℝ} {x v : ℂ} (hv : v.re = 0)
    (hfar : ∀ k : ℤ, |v.im| < |x.im - k * s|) (a₁ a₂ c₁ c₂ : ℤ) :
    x + v ∈ gridRect s a₁ a₂ c₁ c₂ ↔ x ∈ gridRect s a₁ a₂ c₁ c₂ := by
  have hd : ∀ k : ℤ, |(x + v).im - x.im| < |x.im - k * s| := fun k => by
    rw [Complex.add_im, add_sub_cancel_left]
    exact hfar k
  change (a₁ : ℝ) * s ≤ (x + v).re ∧ (x + v).re ≤ a₂ * s ∧ (c₁ : ℝ) * s ≤ (x + v).im ∧
      (x + v).im ≤ c₂ * s ↔
    (a₁ : ℝ) * s ≤ x.re ∧ x.re ≤ a₂ * s ∧ (c₁ : ℝ) * s ≤ x.im ∧ x.im ≤ c₂ * s
  rw [le_iff_le_of_le_abs_sub le_rfl (hd c₁), le_iff_le_of_le_abs_sub' le_rfl (hd c₂),
    Complex.add_re, hv, add_zero]

/-- Horizontal shifts as in `add_mem_gridRect_iff_of_im_eq_zero` preserve membership in
`gridSquares s S`. -/
theorem add_mem_gridSquares_iff_of_im_eq_zero {s : ℝ} {x v : ℂ} (hv : v.im = 0)
    (hfar : ∀ k : ℤ, |v.re| < |x.re - k * s|) (S : Set (ℤ × ℤ)) :
    x + v ∈ gridSquares s S ↔ x ∈ gridSquares s S := by
  simp only [gridSquares, Set.mem_iUnion, add_mem_gridRect_iff_of_im_eq_zero hv hfar]

/-- Vertical shifts as in `add_mem_gridRect_iff_of_re_eq_zero` preserve membership in
`gridSquares s S`. -/
theorem add_mem_gridSquares_iff_of_re_eq_zero {s : ℝ} {x v : ℂ} (hv : v.re = 0)
    (hfar : ∀ k : ℤ, |v.im| < |x.im - k * s|) (S : Set (ℤ × ℤ)) :
    x + v ∈ gridSquares s S ↔ x ∈ gridSquares s S := by
  simp only [gridSquares, Set.mem_iUnion, add_mem_gridRect_iff_of_re_eq_zero hv hfar]

/-- **Unions of closed grid squares along an open edge.** If `y` and `b` lie on the grid lines,
`|y - b| < r ≤ s` and `b` is at distance at least `r` of the vertices, then `y` and `b` lie in the
same unions of closed grid squares. -/
theorem mem_gridSquares_iff_of_le_infDist {s r : ℝ} (hs : 0 < s) (hr : r ≤ s) {y b : ℂ}
    (hy : y ∈ gridLines s) (hb : b ∈ gridLines s) (hd : dist y b < r)
    (hfar : r ≤ infDist b (vertices s)) (S : Set (ℤ × ℤ)) :
    y ∈ gridSquares s S ↔ b ∈ gridSquares s S := by
  simp only [gridSquares, Set.mem_iUnion, mem_gridRect_iff_of_le_infDist hs hr hy hb hd hfar]

/-- **Interiors of unions of closed grid squares along an open edge.** Same hypotheses as
`mem_gridSquares_iff_of_le_infDist`: `y` is an interior point of `gridSquares s S` if and only if
`b` is. -/
theorem mem_interior_gridSquares_iff_of_le_infDist {s r : ℝ} (hs : 0 < s) (hr : r ≤ s) {y b : ℂ}
    (hy : y ∈ gridLines s) (hb : b ∈ gridLines s) (hd : dist y b < r)
    (hfar : r ≤ infDist b (vertices s)) (S : Set (ℤ × ℤ)) :
    y ∈ interior (gridSquares s S) ↔ b ∈ interior (gridSquares s S) := by
  have hre := abs_re_sub_lt_of_dist_lt hd
  have him := abs_im_sub_lt_of_dist_lt hd
  have hyb : y = b + (y - b) := by ring
  rw [hyb]
  rcases eq_re_or_eq_im_of_le_infDist hs hr hy hb hd hfar with ⟨he, hk⟩ | ⟨he, hk⟩
  · refine add_mem_interior_iff_of_forall_dist_lt (sub_pos.2 him) fun x hx =>
      add_mem_gridSquares_iff_of_re_eq_zero (by rw [Complex.sub_re, he, sub_self]) (fun k => ?_) S
    have h1 := abs_im_sub_lt_of_dist_lt hx
    have h2 := hk k
    have h3 := abs_sub_le b.im x.im (k * s)
    rw [abs_sub_comm b.im x.im] at h3
    rw [Complex.sub_im]
    linarith
  · refine add_mem_interior_iff_of_forall_dist_lt (sub_pos.2 hre) fun x hx =>
      add_mem_gridSquares_iff_of_im_eq_zero (by rw [Complex.sub_im, he, sub_self]) (fun k => ?_) S
    have h1 := abs_re_sub_lt_of_dist_lt hx
    have h2 := hk k
    have h3 := abs_sub_le b.re x.re (k * s)
    rw [abs_sub_comm b.re x.re] at h3
    rw [Complex.sub_re]
    linarith

end GridCells

end LatticeProb
