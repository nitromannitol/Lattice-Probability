import LatticeProb.Walk.CellConfigInterpolationDiameter

/-!
# Boundary cells and interpolated walks

Before a walk on a cell configuration reaches a cell meeting the boundary of an open convex
set, its interpolated path remains in the set on each completed holding interval. The
representative of a boundary cell is at most one cell diameter from the boundary.
-/

set_option autoImplicit false

noncomputable section

open Set
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigBoundary

variable (H : CellConfig)

/-- A connected cell meeting an open set and avoiding its frontier is contained in the set. -/
theorem cell_subset_of_meets_of_avoids_frontier (hH : H.IsCellConfiguration)
    {U : Set Plane} (hU : IsOpen U) (K : H.cells)
    (hmeet : ((K.1 : Set Plane) ∩ U).Nonempty)
    (havoid : ¬ ((K.1 : Set Plane) ∩ frontier U).Nonempty) :
    (K.1 : Set Plane) ⊆ U := by
  have hcover : (K.1 : Set Plane) ⊆ U ∪ (closure U)ᶜ := by
    intro z hz
    by_cases hzU : z ∈ U
    · exact Or.inl hzU
    · refine Or.inr fun hzc => havoid ⟨z, hz, ?_⟩
      rw [frontier, hU.interior_eq]
      exact ⟨hzc, hzU⟩
  rcases (hH.isConnected K.1 K.2).isPreconnected.subset_or_subset hU
      isClosed_closure.isOpen_compl
      (Disjoint.mono_left subset_closure disjoint_compl_right) hcover with h | h
  · exact h
  · obtain ⟨z, hzK, hzU⟩ := hmeet
    exact absurd (subset_closure hzU) (h hzK)

/-- Every cell visited before the first boundary cell is contained in the domain. -/
theorem cell_subset_before_boundary (hH : H.IsCellConfiguration) {U : Set Plane}
    (hU : IsOpen U) (ω : ℕ → H.cells) (hstart : ((ω 0).1 : Set Plane) ∩ U |>.Nonempty)
    (hadj : ∀ n, H.Adj (ω n) (ω (n + 1))) {n : ℕ}
    (havoid : ∀ j ≤ n, ¬ (((ω j).1 : Set Plane) ∩ frontier U).Nonempty) :
    ((ω n).1 : Set Plane) ⊆ U := by
  induction n with
  | zero => exact cell_subset_of_meets_of_avoids_frontier H hH hU _ hstart (havoid 0 le_rfl)
  | succ n ih =>
    have hprev := ih (fun j hj => havoid j (Nat.le_succ_of_le hj))
    obtain ⟨z, hz1, hz2⟩ := hH.adj_inter (ω n) (ω (n + 1)) (hadj n)
    exact cell_subset_of_meets_of_avoids_frontier H hH hU _ ⟨z, hz2, hprev hz1⟩
      (havoid (n + 1) le_rfl)

/-- An interpolated segment between two cells visited before the boundary stays in a convex domain. -/
theorem interpolatedPath_mem_before_boundary (hH : H.IsCellConfiguration)
    {U : Set Plane} (hU : IsOpen U) (hconv : Convex ℝ U)
    (p : H.cells → Plane) (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (ω : ℕ → H.cells)
    (hstart : (((ω 0).1 : Set Plane) ∩ U).Nonempty)
    (hadj : ∀ n, H.Adj (ω n) (ω (n + 1))) (hpos : ∀ K, 0 < H.holding K)
    {n : ℕ} {s : ℝ} (h1 : H.jumpTime ω n ≤ s) (h2 : s ≤ H.jumpTime ω (n + 1))
    (havoid : ∀ j ≤ n + 1, ¬ (((ω j).1 : Set Plane) ∩ frontier U).Nonempty) :
    H.interpolatedPath p ω s ∈ U := by
  have hn := cell_subset_before_boundary H hH hU ω hstart hadj
    (fun j hj => havoid j (Nat.le_trans hj (Nat.le_succ n)))
  have hn1 := cell_subset_before_boundary H hH hU ω hstart hadj havoid
  have hd : 0 < H.jumpTime ω (n + 1) - H.jumpTime ω n := by
    rw [H.jumpTime_succ]
    simpa using hpos (ω n)
  rw [H.interpolatedPath_eq_lineMap hpos h1 h2]
  apply hconv.lineMap_mem (hn (hp _)) (hn1 (hp _))
  exact ⟨div_nonneg (sub_nonneg.mpr h1) hd.le,
    (div_le_one hd).2 (sub_le_sub_right h2 _)⟩

/-- If no cell up to index `n` meets the boundary, the interpolated path stays in the
open convex domain at every nonnegative time strictly before the `n`th jump time. -/
theorem interpolatedPath_mem_before_jumpTime (hH : H.IsCellConfiguration)
    {U : Set Plane} (hU : IsOpen U) (hconv : Convex ℝ U)
    (p : H.cells → Plane) (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (ω : ℕ → H.cells)
    (hstart : (((ω 0).1 : Set Plane) ∩ U).Nonempty)
    (hadj : ∀ n, H.Adj (ω n) (ω (n + 1))) (hpos : ∀ K, 0 < H.holding K)
    (hunb : H.JumpTimesUnbounded ω) {n : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (hst : s < H.jumpTime ω n)
    (havoid : ∀ j ≤ n, ¬ (((ω j).1 : Set Plane) ∩ frontier U).Nonempty) :
    H.interpolatedPath p ω s ∈ U := by
  obtain ⟨j, hj1, hj2⟩ := H.exists_mem_Ico hpos hunb hs
  have hjn : j < n := by
    by_contra h
    have hmono := (H.jumpTime_strictMono (ω := ω) hpos).monotone (Nat.le_of_not_gt h)
    exact (not_lt_of_ge (hmono.trans hj1)) hst
  exact interpolatedPath_mem_before_boundary H hH hU hconv p hp ω hstart hadj hpos hj1 hj2.le
    (fun k hk => havoid k (Nat.le_trans hk (Nat.succ_le_of_lt hjn)))

/-- A representative of a cell meeting the frontier is within its diameter of a boundary point. -/
theorem exists_frontier_dist_le_diam (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) {U : Set Plane} (K : H.cells)
    (hmeet : ((K.1 : Set Plane) ∩ frontier U).Nonempty) :
    ∃ z ∈ frontier U, dist (p K) z ≤ Metric.diam (K.1 : Set Plane) := by
  obtain ⟨z, hzK, hzU⟩ := hmeet
  exact ⟨z, hzU, Metric.dist_le_diam_of_mem (K.1 : Cell).isCompact.isBounded (hp K) hzK⟩

end LatticeProb.CellConfigBoundary

end
