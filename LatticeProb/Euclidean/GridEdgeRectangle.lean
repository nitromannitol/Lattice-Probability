import LatticeProb.Euclidean.GridStraddle

/-!
# Grid-line points far from the vertices lie on one open grid edge

Fix a mesh `s > 0`, with the grid lines and the vertices `s(ℤ + iℤ)` of `GridCells`. A grid-line
point `b` at distance at least `r` of the vertices (`r ≤ s`) lies on an open edge of the grid, at
distance at least `r` of both of its endpoints, and every grid-line point `y` with `|y - b| < r` lies
on the same open edge (`eq_re_or_eq_im_of_le_infDist`). Consequently `y` and `b` lie on the same side
of every grid line, so they belong to the same closed rectangles with corners at vertices
(`mem_gridRect_iff_of_le_infDist`) and to the same open ones (`mem_gridRectOpen_iff_of_le_infDist`).
-/

open Metric

namespace LatticeProb

namespace GridCells

/-- The closed rectangle `[a₁ s, a₂ s] × [c₁ s, c₂ s]`, with corners at vertices. -/
def gridRect (s : ℝ) (a₁ a₂ c₁ c₂ : ℤ) : Set ℂ :=
  {x | (a₁ : ℝ) * s ≤ x.re ∧ x.re ≤ a₂ * s ∧ (c₁ : ℝ) * s ≤ x.im ∧ x.im ≤ c₂ * s}

/-- The open rectangle `(a₁ s, a₂ s) × (c₁ s, c₂ s)`, with corners at vertices. -/
def gridRectOpen (s : ℝ) (a₁ a₂ c₁ c₂ : ℤ) : Set ℂ :=
  {x | (a₁ : ℝ) * s < x.re ∧ x.re < a₂ * s ∧ (c₁ : ℝ) * s < x.im ∧ x.im < c₂ * s}

/-- A real number `t` at distance at least `r` of `u`, and `t'` with `|t' - t| < r`, lie on the same
side of `u`. -/
theorem le_iff_le_of_le_abs_sub {t t' u r : ℝ} (hfar : r ≤ |t - u|) (hd : |t' - t| < r) :
    u ≤ t' ↔ u ≤ t := by
  have h1 := (abs_lt.1 hd).1
  have h2 := (abs_lt.1 hd).2
  constructor
  · intro h
    by_contra h'
    rw [abs_of_neg (sub_neg.2 (not_le.1 h'))] at hfar
    linarith
  · intro h
    rw [abs_of_nonneg (sub_nonneg.2 h)] at hfar
    linarith

/-- The mirror form of `le_iff_le_of_le_abs_sub`. -/
theorem le_iff_le_of_le_abs_sub' {t t' u r : ℝ} (hfar : r ≤ |t - u|) (hd : |t' - t| < r) :
    t' ≤ u ↔ t ≤ u := by
  have h := le_iff_le_of_le_abs_sub (t := -t) (t' := -t') (u := -u) (r := r)
    (by rwa [show -t - -u = -(t - u) by ring, abs_neg])
    (by rwa [show -t' - -t = -(t' - t) by ring, abs_neg])
  rwa [neg_le_neg_iff, neg_le_neg_iff] at h

/-- The strict form of `le_iff_le_of_le_abs_sub'`. -/
theorem lt_iff_lt_of_le_abs_sub {t t' u r : ℝ} (hfar : r ≤ |t - u|) (hd : |t' - t| < r) :
    u < t' ↔ u < t := by
  rw [← not_le, ← not_le, le_iff_le_of_le_abs_sub' hfar hd]

/-- The strict form of `le_iff_le_of_le_abs_sub`. -/
theorem lt_iff_lt_of_le_abs_sub' {t t' u r : ℝ} (hfar : r ≤ |t - u|) (hd : |t' - t| < r) :
    t' < u ↔ t < u := by
  rw [← not_le, ← not_le, le_iff_le_of_le_abs_sub hfar hd]

/-- The squared coordinate differences of two points at distance `< r`. -/
theorem sq_add_sq_lt_of_dist_lt {y b : ℂ} {r : ℝ} (hd : dist y b < r) :
    (y.re - b.re) ^ 2 + (y.im - b.im) ^ 2 < r ^ 2 := by
  have hr0 : 0 < r := lt_of_le_of_lt dist_nonneg hd
  rw [Complex.dist_eq_re_im, Real.sqrt_lt' hr0] at hd
  exact hd

/-- The real parts of two points at distance `< r` differ by `< r`. -/
theorem abs_re_sub_lt_of_dist_lt {y b : ℂ} {r : ℝ} (hd : dist y b < r) : |y.re - b.re| < r :=
  abs_lt_of_sq_lt_sq (by nlinarith [sq_add_sq_lt_of_dist_lt hd, sq_nonneg (y.im - b.im)])
    (lt_of_le_of_lt dist_nonneg hd).le

/-- The imaginary parts of two points at distance `< r` differ by `< r`. -/
theorem abs_im_sub_lt_of_dist_lt {y b : ℂ} {r : ℝ} (hd : dist y b < r) : |y.im - b.im| < r :=
  abs_lt_of_sq_lt_sq (by nlinarith [sq_add_sq_lt_of_dist_lt hd, sq_nonneg (y.re - b.re)])
    (lt_of_le_of_lt dist_nonneg hd).le

/-- The distance from a point of the vertical grid line `Re = j s` to the vertex `(j s, k s)`. -/
theorem dist_vertex_of_re_eq {s : ℝ} {b : ℂ} {j : ℤ} (hj : b.re = j * s) (k : ℤ) :
    dist b ⟨j * s, k * s⟩ = |b.im - k * s| := by
  rw [Complex.dist_eq_re_im, hj]
  show √(((j : ℝ) * s - j * s) ^ 2 + (b.im - k * s) ^ 2) = |b.im - k * s|
  rw [sub_self, zero_pow two_ne_zero, zero_add, Real.sqrt_sq_eq_abs]

/-- The distance from a point of the horizontal grid line `Im = m s` to the vertex `(k s, m s)`. -/
theorem dist_vertex_of_im_eq {s : ℝ} {b : ℂ} {m : ℤ} (hm : b.im = m * s) (k : ℤ) :
    dist b ⟨k * s, m * s⟩ = |b.re - k * s| := by
  rw [Complex.dist_eq_re_im, hm]
  show √((b.re - k * s) ^ 2 + ((m : ℝ) * s - m * s) ^ 2) = |b.re - k * s|
  rw [sub_self, zero_pow two_ne_zero, add_zero, Real.sqrt_sq_eq_abs]

/-- **A grid-line point far from the vertices shares its open edge with every close grid-line
point.** If `y` and `b` lie on the grid lines, `|y - b| < r ≤ s` and `b` is at distance at least `r`
of the vertices, then either `b` lies on a vertical grid line, `y` lies on the same one, and the
ordinate of `b` is at distance at least `r` of `sℤ`, or the same holds with the coordinates
exchanged. -/
theorem eq_re_or_eq_im_of_le_infDist {s r : ℝ} (hs : 0 < s) (hr : r ≤ s) {y b : ℂ}
    (hy : y ∈ gridLines s) (hb : b ∈ gridLines s) (hd : dist y b < r)
    (hfar : r ≤ infDist b (vertices s)) :
    (y.re = b.re ∧ ∀ k : ℤ, r ≤ |b.im - k * s|) ∨ (y.im = b.im ∧ ∀ k : ℤ, r ≤ |b.re - k * s|) := by
  have hre := abs_re_sub_lt_of_dist_lt hd
  have him := abs_im_sub_lt_of_dist_lt hd
  have hy' : (∃ j : ℤ, y.re = j * s) ∨ (∃ m : ℤ, y.im = m * s) := hy
  have hb' : (∃ j : ℤ, b.re = j * s) ∨ (∃ m : ℤ, b.im = m * s) := hb
  rcases hb' with ⟨j, hj⟩ | ⟨m, hm⟩
  · have hk : ∀ k : ℤ, r ≤ |b.im - k * s| := fun k =>
      hfar.trans ((infDist_le_dist_of_mem (show (⟨(j : ℝ) * s, (k : ℝ) * s⟩ : ℂ) ∈ vertices s from ⟨j, k, rfl⟩)).trans (dist_vertex_of_re_eq hj k).le)
    refine Or.inl ⟨?_, hk⟩
    rcases hy' with ⟨j', hj'⟩ | ⟨m', hm'⟩
    · have hjj : j' = j := by
        rw [hj', hj] at hre
        exact int_eq_of_abs_sub_lt hs (hre.trans_le hr)
      rw [hj', hj, hjj]
    · rw [hm', abs_sub_comm] at him
      exact absurd him (not_lt.2 (hk m'))
  · have hk : ∀ k : ℤ, r ≤ |b.re - k * s| := fun k =>
      hfar.trans ((infDist_le_dist_of_mem (show (⟨(k : ℝ) * s, (m : ℝ) * s⟩ : ℂ) ∈ vertices s from ⟨k, m, rfl⟩)).trans (dist_vertex_of_im_eq hm k).le)
    refine Or.inr ⟨?_, hk⟩
    rcases hy' with ⟨j', hj'⟩ | ⟨m', hm'⟩
    · rw [hj', abs_sub_comm] at hre
      exact absurd hre (not_lt.2 (hk j'))
    · have hmm : m' = m := by
        rw [hm', hm] at him
        exact int_eq_of_abs_sub_lt hs (him.trans_le hr)
      rw [hm', hm, hmm]

/-- **Closed rectangles with corners at vertices.** If `y` and `b` lie on the grid lines,
`|y - b| < r ≤ s` and `b` is at distance at least `r` of the vertices, then `y` and `b` lie in the
same closed rectangles `[a₁ s, a₂ s] × [c₁ s, c₂ s]`. -/
theorem mem_gridRect_iff_of_le_infDist {s r : ℝ} (hs : 0 < s) (hr : r ≤ s) {y b : ℂ}
    (hy : y ∈ gridLines s) (hb : b ∈ gridLines s) (hd : dist y b < r)
    (hfar : r ≤ infDist b (vertices s)) (a₁ a₂ c₁ c₂ : ℤ) :
    y ∈ gridRect s a₁ a₂ c₁ c₂ ↔ b ∈ gridRect s a₁ a₂ c₁ c₂ := by
  have hre := abs_re_sub_lt_of_dist_lt hd
  have him := abs_im_sub_lt_of_dist_lt hd
  change (a₁ : ℝ) * s ≤ y.re ∧ y.re ≤ a₂ * s ∧ (c₁ : ℝ) * s ≤ y.im ∧ y.im ≤ c₂ * s ↔
    (a₁ : ℝ) * s ≤ b.re ∧ b.re ≤ a₂ * s ∧ (c₁ : ℝ) * s ≤ b.im ∧ b.im ≤ c₂ * s
  rcases eq_re_or_eq_im_of_le_infDist hs hr hy hb hd hfar with ⟨he, hk⟩ | ⟨he, hk⟩
  · rw [he, le_iff_le_of_le_abs_sub (hk c₁) him, le_iff_le_of_le_abs_sub' (hk c₂) him]
  · rw [he, le_iff_le_of_le_abs_sub (hk a₁) hre, le_iff_le_of_le_abs_sub' (hk a₂) hre]

/-- **Open rectangles with corners at vertices.** Same hypotheses as
`mem_gridRect_iff_of_le_infDist`: `y` and `b` lie in the same open rectangles
`(a₁ s, a₂ s) × (c₁ s, c₂ s)`. -/
theorem mem_gridRectOpen_iff_of_le_infDist {s r : ℝ} (hs : 0 < s) (hr : r ≤ s) {y b : ℂ}
    (hy : y ∈ gridLines s) (hb : b ∈ gridLines s) (hd : dist y b < r)
    (hfar : r ≤ infDist b (vertices s)) (a₁ a₂ c₁ c₂ : ℤ) :
    y ∈ gridRectOpen s a₁ a₂ c₁ c₂ ↔ b ∈ gridRectOpen s a₁ a₂ c₁ c₂ := by
  have hre := abs_re_sub_lt_of_dist_lt hd
  have him := abs_im_sub_lt_of_dist_lt hd
  change (a₁ : ℝ) * s < y.re ∧ y.re < a₂ * s ∧ (c₁ : ℝ) * s < y.im ∧ y.im < c₂ * s ↔
    (a₁ : ℝ) * s < b.re ∧ b.re < a₂ * s ∧ (c₁ : ℝ) * s < b.im ∧ b.im < c₂ * s
  rcases eq_re_or_eq_im_of_le_infDist hs hr hy hb hd hfar with ⟨he, hk⟩ | ⟨he, hk⟩
  · rw [he, lt_iff_lt_of_le_abs_sub (hk c₁) him, lt_iff_lt_of_le_abs_sub' (hk c₂) him]
  · rw [he, lt_iff_lt_of_le_abs_sub (hk a₁) hre, lt_iff_lt_of_le_abs_sub' (hk a₂) hre]

end GridCells

end LatticeProb
