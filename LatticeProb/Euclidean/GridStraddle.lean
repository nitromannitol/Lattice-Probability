import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Two close points of the grid lines in different cells are close to a vertex

Fix a mesh `s > 0`. The *grid lines* are the points of the plane with a coordinate in `sℤ`,
the *vertices* are the points of `s(ℤ + iℤ)`, and the *cell* of a point `y` is the pair
`(⌊Re y / s⌋, ⌊Im y / s⌋)` of integer parts (half-open cells `[ks, (k+1)s) × [ms, (m+1)s)`).

**Main result.**  If `y` and `b` lie on the grid lines, `|y - b| < r ≤ s`, and `y` and `b` lie in
different cells, then `b` is at distance `< r` of a vertex (`exists_vertex_of_cellIndex_ne`).
In particular `dist b (vertices) < r` (`infDist_vertices_lt_of_cellIndex_ne`) and, contrapositively,
a grid-line point `b` at distance at least `r` of the vertices has the same cell as every
grid-line point within distance `r` (`cellIndex_eq_of_le_infDist_vertices`).

The proof: a different cell forces a grid line `x = ks` or `y = ks` between the two points, on
which neither point can lie unless it sits on it; the other coordinates then force a vertex on
that line within distance `r`.
-/

open Metric

namespace LatticeProb

namespace GridCells

/-- The vertices `s(ℤ + iℤ)` of the grid of mesh `s`. -/
def vertices (s : ℝ) : Set ℂ := {p | ∃ m n : ℤ, p = ⟨m * s, n * s⟩}

/-- The grid lines of mesh `s`: the points with a coordinate in `sℤ`. -/
def gridLines (s : ℝ) : Set ℂ := {y | (∃ j : ℤ, y.re = j * s) ∨ (∃ m : ℤ, y.im = m * s)}

/-- The cell of `y` for the grid of mesh `s`: the integer parts of the coordinates over `s`. -/
noncomputable def cellIndex (s : ℝ) (y : ℂ) : ℤ × ℤ := (⌊y.re / s⌋, ⌊y.im / s⌋)

/-- Two integer multiples of `s` at distance `< s` are equal. -/
theorem int_eq_of_abs_sub_lt {s : ℝ} (hs : 0 < s) {j k : ℤ} (h : |(j : ℝ) * s - k * s| < s) :
    j = k := by
  by_contra hne
  have h1 : (1 : ℝ) ≤ |(j : ℝ) - k| := by
    have := Int.one_le_abs (sub_ne_zero.2 hne)
    exact_mod_cast this
  have h2 : |(j : ℝ) * s - k * s| = |(j : ℝ) - k| * s := by
    rw [← sub_mul, abs_mul, abs_of_pos hs]
  rw [h2] at h
  nlinarith

/-- If the integer parts of `u / s` and `v / s` differ, a point `k s` of `sℤ` lies in
`(min u v, max u v]`, in the half-open sense of the cells. -/
theorem exists_int_between_of_floor_ne {s : ℝ} (hs : 0 < s) {u v : ℝ}
    (h : ⌊u / s⌋ ≠ ⌊v / s⌋) :
    ∃ k : ℤ, (u < k * s ∧ k * s ≤ v) ∨ (v < k * s ∧ k * s ≤ u) := by
  rcases lt_or_gt_of_ne h with h | h
  · refine ⟨⌊v / s⌋, Or.inl ⟨?_, ?_⟩⟩
    · have h1 : u / s < ⌊v / s⌋ := by
        have h0 := Int.lt_floor_add_one (u / s)
        have h2 : ((⌊u / s⌋ : ℤ) : ℝ) + 1 ≤ ⌊v / s⌋ := by
          exact_mod_cast Int.add_one_le_iff.2 h
        linarith
      rwa [div_lt_iff₀ hs] at h1
    · have h0 := Int.floor_le (v / s)
      rwa [le_div_iff₀ hs] at h0
  · refine ⟨⌊u / s⌋, Or.inr ⟨?_, ?_⟩⟩
    · have h1 : v / s < ⌊u / s⌋ := by
        have h0 := Int.lt_floor_add_one (v / s)
        have h2 : ((⌊v / s⌋ : ℤ) : ℝ) + 1 ≤ ⌊u / s⌋ := by
          exact_mod_cast Int.add_one_le_iff.2 h
        linarith
      rwa [div_lt_iff₀ hs] at h1
    · have h0 := Int.floor_le (u / s)
      rwa [le_div_iff₀ hs] at h0

theorem sq_le_of_between {a K c : ℝ} (h : (a ≤ K ∧ K ≤ c) ∨ (c ≤ K ∧ K ≤ a)) :
    (c - K) ^ 2 ≤ (a - c) ^ 2 ∧ (a - K) ^ 2 ≤ (a - c) ^ 2 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · constructor <;>
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2), sq_nonneg (K - a),
        sq_nonneg (c - K)]
  · constructor <;>
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2), sq_nonneg (K - c),
        sq_nonneg (a - K)]

/-- One-coordinate form of the main estimate: the first coordinates `a, c` of the two points are
separated by the value `k s`, and each point has a coordinate in `sℤ`. -/
theorem exists_int_of_crossing {s r : ℝ} (hs : 0 < s) (hr : r ≤ s) (hr0 : 0 < r)
    {a a' c c' : ℝ} {k : ℤ}
    (hy : (∃ j : ℤ, a = j * s) ∨ (∃ m : ℤ, a' = m * s))
    (hb : (∃ j : ℤ, c = j * s) ∨ (∃ m : ℤ, c' = m * s))
    (hd : (a - c) ^ 2 + (a' - c') ^ 2 < r ^ 2)
    (hcr : (a < k * s ∧ k * s ≤ c) ∨ (c < k * s ∧ k * s ≤ a)) :
    ∃ m : ℤ, (c - k * s) ^ 2 + (c' - m * s) ^ 2 < r ^ 2 := by
  have hbet : (a ≤ k * s ∧ k * s ≤ c) ∨ (c ≤ k * s ∧ k * s ≤ a) :=
    hcr.imp (fun h => ⟨h.1.le, h.2⟩) (fun h => ⟨h.1.le, h.2⟩)
  obtain ⟨hle1, hle2⟩ := sq_le_of_between hbet
  have hsq : (a - c) ^ 2 < r ^ 2 := lt_of_le_of_lt (le_add_of_nonneg_right (sq_nonneg _)) hd
  have hKa : |a - k * s| < s :=
    lt_of_lt_of_le (abs_lt_of_sq_lt_sq (lt_of_le_of_lt hle2 hsq) hr0.le) hr
  have hKc : |c - k * s| < s :=
    lt_of_lt_of_le (abs_lt_of_sq_lt_sq (lt_of_le_of_lt hle1 hsq) hr0.le) hr
  rcases hy with ⟨j, hj⟩ | ⟨m, hm⟩
  · have hjk : j = k := int_eq_of_abs_sub_lt hs (by rwa [← hj])
    have haK : a = k * s := by rw [hj, hjk]
    rcases hcr with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact absurd haK h1.ne
    · rcases hb with ⟨j', hj'⟩ | ⟨m', hm'⟩
      · have hjk' : j' = k := int_eq_of_abs_sub_lt hs (by rwa [← hj'])
        have : c = k * s := by rw [hj', hjk']
        exact absurd this h1.ne
      · refine ⟨m', ?_⟩
        have : c' - m' * s = 0 := sub_eq_zero.2 hm'
        rw [this]
        nlinarith [sq_nonneg (a' - c')]
  · refine ⟨m, ?_⟩
    have : (c' - m * s) ^ 2 = (a' - c') ^ 2 := by rw [← hm]; ring
    rw [this]
    linarith

/-- **Close grid-line points in different cells are close to a vertex.**  If `y, b` lie on the
grid lines of mesh `s`, `|y - b| < r ≤ s` and `y, b` are in different cells, there is a vertex
at distance `< r` of `b`. -/
theorem exists_vertex_of_cellIndex_ne {s r : ℝ} (hs : 0 < s) (hr : r ≤ s) {y b : ℂ}
    (hy : y ∈ gridLines s) (hb : b ∈ gridLines s) (hd : dist y b < r)
    (hne : cellIndex s y ≠ cellIndex s b) : ∃ p ∈ vertices s, dist b p < r := by
  have hr0 : 0 < r := lt_of_le_of_lt dist_nonneg hd
  have hd2 : (y.re - b.re) ^ 2 + (y.im - b.im) ^ 2 < r ^ 2 := by
    rw [Complex.dist_eq_re_im, Real.sqrt_lt' hr0] at hd
    exact hd
  have hy' : (∃ j : ℤ, y.re = j * s) ∨ (∃ m : ℤ, y.im = m * s) := hy
  have hb' : (∃ j : ℤ, b.re = j * s) ∨ (∃ m : ℤ, b.im = m * s) := hb
  have hfl : ⌊y.re / s⌋ ≠ ⌊b.re / s⌋ ∨ ⌊y.im / s⌋ ≠ ⌊b.im / s⌋ := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    exact hne (Prod.ext hcon.1 hcon.2)
  rcases hfl with h | h
  · obtain ⟨k, hk⟩ := exists_int_between_of_floor_ne hs h
    obtain ⟨m, hm⟩ := exists_int_of_crossing hs hr hr0 hy' hb' hd2 hk
    refine ⟨⟨k * s, m * s⟩, ⟨k, m, rfl⟩, ?_⟩
    rw [Complex.dist_eq_re_im, Real.sqrt_lt' hr0]
    simpa using hm
  · obtain ⟨k, hk⟩ := exists_int_between_of_floor_ne hs h
    obtain ⟨m, hm⟩ := exists_int_of_crossing hs hr hr0 hy'.symm hb'.symm
      (by linarith) hk
    refine ⟨⟨m * s, k * s⟩, ⟨m, k, rfl⟩, ?_⟩
    rw [Complex.dist_eq_re_im, Real.sqrt_lt' hr0]
    simp only
    linarith

/-- The distance from `b` to the vertices is `< r`. -/
theorem infDist_vertices_lt_of_cellIndex_ne {s r : ℝ} (hs : 0 < s) (hr : r ≤ s) {y b : ℂ}
    (hy : y ∈ gridLines s) (hb : b ∈ gridLines s) (hd : dist y b < r)
    (hne : cellIndex s y ≠ cellIndex s b) : infDist b (vertices s) < r := by
  obtain ⟨p, hp, hbp⟩ := exists_vertex_of_cellIndex_ne hs hr hy hb hd hne
  exact lt_of_le_of_lt (infDist_le_dist_of_mem hp) hbp

/-- A grid-line point `b` at distance at least `r` of the vertices has the same cell as every
grid-line point `y` within distance `r` of it (`r ≤ s`). -/
theorem cellIndex_eq_of_le_infDist_vertices {s r : ℝ} (hs : 0 < s) (hr : r ≤ s) {y b : ℂ}
    (hy : y ∈ gridLines s) (hb : b ∈ gridLines s) (hd : dist y b < r)
    (hfar : r ≤ infDist b (vertices s)) : cellIndex s y = cellIndex s b := by
  by_contra hne
  exact absurd (infDist_vertices_lt_of_cellIndex_ne hs hr hy hb hd hne) (not_lt.2 hfar)

end GridCells

end LatticeProb
