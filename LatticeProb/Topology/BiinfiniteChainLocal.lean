import LatticeProb.Topology.PolygonalChainLocal
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Local structure of a simple bi-infinite polygonal chain at an interior edge point

Let `u : ℤ → ℂ` be a bi-infinite sequence of vertices with `u n → a` as `n → -∞` and
`u n → b` as `n → +∞`.  Suppose consecutive edges `[u n, u (n+1)]` and `[u (n+1), u (n+2)]` meet
only at `u (n+1)`, edges at index distance at least `2` are disjoint, consecutive vertices are
distinct, and the limit points `a`, `b` lie on no edge.  Then near a point `y` of the open edge
`(u k, u (k+1))` the set `{a, b} ∪ ⋃ₙ [u n, u (n+1)]` coincides with the edge `[u k, u (k+1)]`.

At a vertex `u j` the chain coincides, near `u j`, with the union of the two segments from `u j`
to `u (j-1)` and `u (j+1)`, which do not point in the same direction.

* `LatticeProb.Topology.notMem_segment_of_mem_openSegment_of_ne`: `y` lies on no other edge.
* `LatticeProb.Topology.exists_inter_ball_eq_biUnion_finset`: localisation to finitely many edges.
* `LatticeProb.Topology.exists_inter_ball_eq_segment_of_simple_biinfinite`: the edge statement.
* `LatticeProb.Topology.exists_two_segments_inter_ball_of_vertex` and
  `LatticeProb.Topology.exists_two_segments_inter_ball_of_simple_biinfinite`: two segments.
-/

open Filter Set Metric
open scoped Topology

namespace LatticeProb.Topology

/-- A point of the open edge `(u k, u (k+1))` lies on no other edge of a simple chain. -/
theorem notMem_segment_of_mem_openSegment_of_ne {u : ℤ → ℂ} (hne : ∀ n, u n ≠ u (n + 1))
    (hadj : ∀ n, segment ℝ (u n) (u (n + 1)) ∩ segment ℝ (u (n + 1)) (u (n + 2)) ⊆ {u (n + 1)})
    (hfar : ∀ n m : ℤ, n + 2 ≤ m →
      Disjoint (segment ℝ (u n) (u (n + 1))) (segment ℝ (u m) (u (m + 1))))
    {k : ℤ} {y : ℂ} (hy : y ∈ openSegment ℝ (u k) (u (k + 1))) {n : ℤ} (hn : n ≠ k) :
    y ∉ segment ℝ (u n) (u (n + 1)) := by
  have hyk : y ∈ segment ℝ (u k) (u (k + 1)) := openSegment_subset_segment ℝ _ _ hy
  have hy0 : y ≠ u k := fun h => by
    rw [h] at hy
    exact hne k (left_mem_openSegment_iff.1 hy)
  have hy1 : y ≠ u (k + 1) := fun h => by
    rw [h] at hy
    exact hne k (right_mem_openSegment_iff.1 hy)
  intro hyn
  rcases (by omega : n + 2 ≤ k ∨ n = k - 1 ∨ n = k + 1 ∨ k + 2 ≤ n) with h | h | h | h
  · exact Set.disjoint_left.1 (hfar n k h) hyn hyk
  · subst h
    have h2 := hadj (k - 1)
    simp only [sub_add_cancel] at h2 hyn
    rw [show k - 1 + 2 = k + 1 by ring] at h2
    exact hy0 (h2 ⟨hyn, hyk⟩)
  · subst h
    rw [show k + 1 + 1 = k + 2 by ring] at hyn
    exact hy1 (hadj k ⟨hyk, hyn⟩)
  · exact Set.disjoint_left.1 (hfar k n h) hyk hyn

/-- **Localisation to finitely many edges.** If `y` is neither end and lies on no edge outside the
finite index set `I`, then in a small ball around `y` the chain together with its two ends
coincides with the union of the edges indexed by `I`. -/
theorem exists_inter_ball_eq_biUnion_finset {u : ℤ → ℂ} {a b : ℂ}
    (ha : Tendsto u atBot (𝓝 a)) (hb : Tendsto u atTop (𝓝 b)) (I : Finset ℤ) {y : ℂ}
    (hya : y ≠ a) (hyb : y ≠ b) (hI : ∀ n, n ∉ I → y ∉ segment ℝ (u n) (u (n + 1)))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r > 0, r ≤ ρ ∧
      insert a (insert b (⋃ n, segment ℝ (u n) (u (n + 1)))) ∩ ball y r =
        (⋃ n ∈ I, segment ℝ (u n) (u (n + 1))) ∩ ball y r := by
  have hya' : 0 < dist y a := dist_pos.2 hya
  have hyb' : 0 < dist y b := dist_pos.2 hyb
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℤ, ∀ n ≤ N1, u n ∈ ball a (dist y a / 2) :=
    eventually_atBot.1 (ha.eventually (ball_mem_nhds a (half_pos hya')))
  obtain ⟨N2, hN2⟩ : ∃ N2 : ℤ, ∀ n ≥ N2, u n ∈ ball b (dist y b / 2) :=
    eventually_atTop.1 (hb.eventually (ball_mem_nhds b (half_pos hyb')))
  have hleft : ∀ n ≤ N1 - 1, segment ℝ (u n) (u (n + 1)) ⊆ ball a (dist y a / 2) :=
    fun n hn => (convex_ball a _).segment_subset (hN1 n (by omega)) (hN1 (n + 1) (by omega))
  have hright : ∀ n ≥ N2, segment ℝ (u n) (u (n + 1)) ⊆ ball b (dist y b / 2) :=
    fun n hn => (convex_ball b _).segment_subset (hN2 n hn) (hN2 (n + 1) (by omega))
  have hS : IsCompact (⋃ n ∈ (Finset.Ico N1 N2 \ I : Finset ℤ), segment ℝ (u n) (u (n + 1))) := by
    refine Finset.isCompact_biUnion _ fun n _ => ?_
    rw [segment_eq_image' ℝ (u n) (u (n + 1))]
    exact isCompact_Icc.image (by fun_prop)
  have hyS : y ∉ ⋃ n ∈ (Finset.Ico N1 N2 \ I : Finset ℤ), segment ℝ (u n) (u (n + 1)) := by
    simp only [mem_iUnion, not_exists]
    intro n hn hyn
    exact hI n (Finset.mem_sdiff.1 hn).2 hyn
  obtain ⟨r0, hr0, hr0S⟩ := Metric.isOpen_iff.1 hS.isClosed.isOpen_compl y hyS
  refine ⟨min (min r0 ρ) (min (dist y a / 2) (dist y b / 2)),
    lt_min (lt_min hr0 hρ) (lt_min (half_pos hya') (half_pos hyb')),
    (min_le_left _ _).trans (min_le_right _ _), ?_⟩
  set r := min (min r0 ρ) (min (dist y a / 2) (dist y b / 2)) with hr
  have hr0' : r ≤ r0 := (min_le_left _ _).trans (min_le_left _ _)
  have hra : r ≤ dist y a / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrb : r ≤ dist y b / 2 := (min_le_right _ _).trans (min_le_right _ _)
  ext z
  constructor
  · rintro ⟨hz, hzr⟩
    refine ⟨?_, hzr⟩
    have hzy : dist z y < r := mem_ball.1 hzr
    rcases hz with h | h | hz
    · exfalso
      rw [h] at hzy
      have := dist_comm y a
      linarith
    · exfalso
      rw [h] at hzy
      have := dist_comm y b
      linarith
    · obtain ⟨n, hn⟩ := mem_iUnion.1 hz
      by_cases hnI : n ∈ I
      · exact mem_iUnion₂.2 ⟨n, hnI, hn⟩
      · exfalso
        by_cases hn1 : n ≤ N1 - 1
        · have h1 := mem_ball.1 (hleft n hn1 hn)
          have := dist_triangle y z a
          have := dist_comm y z
          linarith
        by_cases hn2 : N2 ≤ n
        · have h1 := mem_ball.1 (hright n hn2 hn)
          have := dist_triangle y z b
          have := dist_comm y z
          linarith
        · have hzS : z ∈ ⋃ n ∈ (Finset.Ico N1 N2 \ I : Finset ℤ), segment ℝ (u n) (u (n + 1)) :=
            mem_iUnion₂.2 ⟨n, Finset.mem_sdiff.2
              ⟨Finset.mem_Ico.2 ⟨by omega, by omega⟩, hnI⟩, hn⟩
          exact hr0S (mem_ball.2 (hzy.trans_le hr0')) hzS
  · rintro ⟨hz, hzr⟩
    obtain ⟨n, hnI, hn⟩ := mem_iUnion₂.1 hz
    exact ⟨mem_insert_of_mem _ (mem_insert_of_mem _ (mem_iUnion.2 ⟨n, hn⟩)), hzr⟩

/-- **Local structure at an interior edge point.** Near a point `y` of the open edge
`(u k, u (k+1))` of a simple bi-infinite chain with ends `a`, `b`, the union of the chain and its
two ends coincides with the edge `[u k, u (k+1)]`, in a ball of radius at most the distances from
`y` to the two endpoints of the edge. -/
theorem exists_inter_ball_eq_segment_of_simple_biinfinite {u : ℤ → ℂ} {a b : ℂ}
    (hne : ∀ n, u n ≠ u (n + 1))
    (hadj : ∀ n, segment ℝ (u n) (u (n + 1)) ∩ segment ℝ (u (n + 1)) (u (n + 2)) ⊆ {u (n + 1)})
    (hfar : ∀ n m : ℤ, n + 2 ≤ m →
      Disjoint (segment ℝ (u n) (u (n + 1))) (segment ℝ (u m) (u (m + 1))))
    (ha : Tendsto u atBot (𝓝 a)) (hb : Tendsto u atTop (𝓝 b))
    (haγ : ∀ n, a ∉ segment ℝ (u n) (u (n + 1))) (hbγ : ∀ n, b ∉ segment ℝ (u n) (u (n + 1)))
    {k : ℤ} {y : ℂ} (hy : y ∈ openSegment ℝ (u k) (u (k + 1))) :
    ∃ r > 0, r ≤ ‖u k - y‖ ∧ r ≤ ‖u (k + 1) - y‖ ∧
      insert a (insert b (⋃ n, segment ℝ (u n) (u (n + 1)))) ∩ Metric.ball y r =
        segment ℝ (u k) (u (k + 1)) ∩ Metric.ball y r := by
  have hyk : y ∈ segment ℝ (u k) (u (k + 1)) := openSegment_subset_segment ℝ _ _ hy
  have hy0 : y ≠ u k := fun h => by
    rw [h] at hy
    exact hne k (left_mem_openSegment_iff.1 hy)
  have hy1 : y ≠ u (k + 1) := fun h => by
    rw [h] at hy
    exact hne k (right_mem_openSegment_iff.1 hy)
  have hk0 : 0 < ‖u k - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hy0.symm)
  have hk1 : 0 < ‖u (k + 1) - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hy1.symm)
  obtain ⟨r, hr, hrρ, hEq⟩ := exists_inter_ball_eq_biUnion_finset ha hb {k}
    (fun h => haγ k (h ▸ hyk)) (fun h => hbγ k (h ▸ hyk))
    (fun n hn => notMem_segment_of_mem_openSegment_of_ne hne hadj hfar hy
      (by simpa using hn)) (lt_min hk0 hk1)
  refine ⟨r, hr, hrρ.trans (min_le_left _ _), hrρ.trans (min_le_right _ _), ?_⟩
  rw [hEq]
  simp

/-- **Local structure at a vertex.** Near the vertex `u j` of a simple bi-infinite chain with ends
`a`, `b`, the union of the chain and its two ends is the union of the two segments from `u j` to
its neighbours `u (j-1)` and `u (j+1)`, which do not point in the same direction from `u j`. -/
theorem exists_two_segments_inter_ball_of_vertex {u : ℤ → ℂ} {a b : ℂ}
    (hne : ∀ n, u n ≠ u (n + 1))
    (hadj : ∀ n, segment ℝ (u n) (u (n + 1)) ∩ segment ℝ (u (n + 1)) (u (n + 2)) ⊆ {u (n + 1)})
    (hfar : ∀ n m : ℤ, n + 2 ≤ m →
      Disjoint (segment ℝ (u n) (u (n + 1))) (segment ℝ (u m) (u (m + 1))))
    (ha : Tendsto u atBot (𝓝 a)) (hb : Tendsto u atTop (𝓝 b))
    (haγ : ∀ n, a ∉ segment ℝ (u n) (u (n + 1))) (hbγ : ∀ n, b ∉ segment ℝ (u n) (u (n + 1)))
    (j : ℤ) :
    ∃ r > 0, ∃ c d : ℂ, c ≠ u j ∧ d ≠ u j ∧ (∀ t : ℝ, 0 < t → d - u j ≠ t • (c - u j)) ∧
      r ≤ ‖c - u j‖ ∧ r ≤ ‖d - u j‖ ∧
      insert a (insert b (⋃ n, segment ℝ (u n) (u (n + 1)))) ∩ Metric.ball (u j) r =
        (segment ℝ (u j) c ∪ segment ℝ (u j) d) ∩ Metric.ball (u j) r := by
  have hne' : u (j - 1) ≠ u j := by
    have := hne (j - 1)
    rwa [sub_add_cancel] at this
  have hne2 : u j ≠ u (j + 1) := hne j
  have hyr : u j ∈ segment ℝ (u j) (u (j + 1)) := left_mem_segment ℝ _ _
  have hyl' : u j ∈ segment ℝ (u (j - 1)) (u j) := right_mem_segment ℝ _ _
  have hyl : u j ∈ segment ℝ (u (j - 1)) (u (j - 1 + 1)) := by
    rw [sub_add_cancel]; exact hyl'
  have hc : 0 < ‖u (j - 1) - u j‖ := norm_pos_iff.2 (sub_ne_zero.2 hne')
  have hd : 0 < ‖u (j + 1) - u j‖ := norm_pos_iff.2 (sub_ne_zero.2 hne2.symm)
  have hI : ∀ n, n ∉ ({j - 1, j} : Finset ℤ) → u j ∉ segment ℝ (u n) (u (n + 1)) := by
    intro n hn hyn
    have hn' : n ≠ j - 1 ∧ n ≠ j := by simpa using hn
    rcases (by omega : n + 2 ≤ j - 1 ∨ n = j - 2 ∨ n = j + 1 ∨ j + 2 ≤ n) with h | h | h | h
    · exact Set.disjoint_left.1 (hfar n (j - 1) h) hyn hyl
    · subst h
      have h2 := hadj (j - 2)
      rw [show j - 2 + 1 = j - 1 by ring, show j - 2 + 2 = j by ring] at h2
      rw [show j - 2 + 1 = j - 1 by ring] at hyn
      exact hne' (h2 ⟨hyn, hyl'⟩).symm
    · subst h
      have h2 := hadj j
      rw [show j + 1 + 1 = j + 2 by ring] at hyn
      exact hne2 (h2 ⟨hyr, hyn⟩)
    · exact Set.disjoint_left.1 (hfar j n h) hyr hyn
  obtain ⟨r, hr, hrρ, hEq⟩ := exists_inter_ball_eq_biUnion_finset ha hb {j - 1, j}
    (fun h => haγ j (by rw [← h]; exact hyr)) (fun h => hbγ j (by rw [← h]; exact hyr)) hI
    (lt_min hc hd)
  refine ⟨r, hr, u (j - 1), u (j + 1), hne', hne2.symm, ?_, hrρ.trans (min_le_left _ _),
    hrρ.trans (min_le_right _ _), ?_⟩
  · intro t ht h
    have h2 := hadj (j - 1)
    rw [sub_add_cancel, show j - 1 + 2 = j + 1 by ring] at h2
    have h1t : (0 : ℝ) < 1 + t := by linarith
    have hp1 : u j + (1 / (1 + t)) • (u (j + 1) - u j) ∈ segment ℝ (u (j - 1)) (u j) := by
      rw [segment_symm, segment_eq_image' ℝ (u j) (u (j - 1))]
      refine ⟨t / (1 + t), ⟨by positivity, ?_⟩, ?_⟩
      · rw [div_le_one h1t]; linarith
      · simp only []
        rw [h, smul_smul, show 1 / (1 + t) * t = t / (1 + t) by ring]
    have hp2 : u j + (1 / (1 + t)) • (u (j + 1) - u j) ∈ segment ℝ (u j) (u (j + 1)) := by
      rw [segment_eq_image' ℝ (u j) (u (j + 1))]
      refine ⟨1 / (1 + t), ⟨by positivity, ?_⟩, rfl⟩
      rw [div_le_one h1t]; linarith
    have h3 := Set.mem_singleton_iff.1 (h2 ⟨hp1, hp2⟩)
    rcases smul_eq_zero.1 ((add_right_inj (u j)).1 (h3.trans (add_zero _).symm)) with h3 | h3
    · exact absurd h3 (by positivity)
    · exact hne2 (sub_eq_zero.1 h3).symm
  · rw [hEq]
    have h1 : (⋃ n ∈ ({j - 1, j} : Finset ℤ), segment ℝ (u n) (u (n + 1))) =
        segment ℝ (u j) (u (j - 1)) ∪ segment ℝ (u j) (u (j + 1)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, iUnion_iUnion_eq_or_left,
        iUnion_iUnion_eq_left, sub_add_cancel]
      rw [segment_symm]
    rw [h1]

/-- **Local structure at a point of an edge.** Near any point `y` of the edge `[u k, u (k+1)]` of a
simple bi-infinite chain with ends `a`, `b`, the union of the chain and its two ends is the union
of two segments from `y` to points `c`, `d` that do not lie in the same direction from `y`. -/
theorem exists_two_segments_inter_ball_of_simple_biinfinite {u : ℤ → ℂ} {a b : ℂ}
    (hne : ∀ n, u n ≠ u (n + 1))
    (hadj : ∀ n, segment ℝ (u n) (u (n + 1)) ∩ segment ℝ (u (n + 1)) (u (n + 2)) ⊆ {u (n + 1)})
    (hfar : ∀ n m : ℤ, n + 2 ≤ m →
      Disjoint (segment ℝ (u n) (u (n + 1))) (segment ℝ (u m) (u (m + 1))))
    (ha : Tendsto u atBot (𝓝 a)) (hb : Tendsto u atTop (𝓝 b))
    (haγ : ∀ n, a ∉ segment ℝ (u n) (u (n + 1))) (hbγ : ∀ n, b ∉ segment ℝ (u n) (u (n + 1)))
    {k : ℤ} {y : ℂ} (hy : y ∈ segment ℝ (u k) (u (k + 1))) :
    ∃ r > 0, ∃ c d : ℂ, c ≠ y ∧ d ≠ y ∧ (∀ t : ℝ, 0 < t → d - y ≠ t • (c - y)) ∧
      r ≤ ‖c - y‖ ∧ r ≤ ‖d - y‖ ∧
      insert a (insert b (⋃ n, segment ℝ (u n) (u (n + 1)))) ∩ Metric.ball y r =
        (segment ℝ y c ∪ segment ℝ y d) ∩ Metric.ball y r := by
  rw [← insert_endpoints_openSegment] at hy
  simp only [Set.mem_insert_iff] at hy
  rcases hy with h | h | hy
  · subst h
    exact exists_two_segments_inter_ball_of_vertex hne hadj hfar ha hb haγ hbγ k
  · subst h
    exact exists_two_segments_inter_ball_of_vertex hne hadj hfar ha hb haγ hbγ (k + 1)
  · obtain ⟨r, hr, hrc, hrd, hEq⟩ :=
      exists_inter_ball_eq_segment_of_simple_biinfinite hne hadj hfar ha hb haγ hbγ hy
    have hyk : y ∈ segment ℝ (u k) (u (k + 1)) := openSegment_subset_segment ℝ _ _ hy
    have hy0 : y ≠ u k := fun h => by
      rw [h] at hy
      exact hne k (left_mem_openSegment_iff.1 hy)
    have hy1 : y ≠ u (k + 1) := fun h => by
      rw [h] at hy
      exact hne k (right_mem_openSegment_iff.1 hy)
    refine ⟨r, hr, u k, u (k + 1), hy0.symm, hy1.symm, ?_, hrc, hrd, ?_⟩
    · intro t ht h
      obtain ⟨α, β, hα, hβ, hαβ, hyeq⟩ := hy
      obtain rfl : β = 1 - α := by linarith
      subst hyeq
      have h4 : (α + t * (1 - α)) • (u (k + 1) - u k) = 0 := by
        linear_combination (norm := module) h
      rcases smul_eq_zero.1 h4 with h5 | h5
      · have : 0 < α + t * (1 - α) := by
          have : 0 < 1 - α := hβ
          positivity
        linarith
      · exact hne k (sub_eq_zero.1 h5).symm
    · rw [hEq]
      have h1 : segment ℝ (u k) (u (k + 1)) = segment ℝ y (u k) ∪ segment ℝ y (u (k + 1)) :=
        Set.Subset.antisymm (segment_subset_segment_union hyk)
          (Set.union_subset
            ((convex_segment _ _).segment_subset hyk (left_mem_segment ℝ _ _))
            ((convex_segment _ _).segment_subset hyk (right_mem_segment ℝ _ _)))
      rw [h1]

end LatticeProb.Topology
