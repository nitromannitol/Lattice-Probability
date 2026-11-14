import LatticeProb.Walk.CellConfigBoundaryBracket

/-!
# Inner boundary cells

If an inner boundary is separated from the complement of a convex outer domain, a walk
reaching a sufficiently small inner boundary cell remains in the outer domain through that jump.
-/

set_option autoImplicit false

noncomputable section

open Set
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigBoundary

variable (H : CellConfig)

/-- A small cell meeting a boundary stays in any domain containing a suitable neighborhood
of that boundary. -/
theorem cell_subset_of_meets_frontier_of_diam_lt {U V : Set Plane} {r : ℝ}
    (hball : ∀ z ∈ frontier V, Metric.ball z r ⊆ U) (K : H.cells)
    (hmeet : ((K.1 : Set Plane) ∩ frontier V).Nonempty)
    (hdiam : Metric.diam (K.1 : Set Plane) < r) : (K.1 : Set Plane) ⊆ U := by
  obtain ⟨z, hzK, hzV⟩ := hmeet
  intro x hx
  apply hball z hzV
  exact (Metric.mem_ball).2 ((Metric.dist_le_diam_of_mem (K.1 : Cell).isCompact.isBounded
    hx hzK).trans_lt hdiam)

/-- Before and at the first inner-boundary jump, the interpolated path remains in the
larger convex domain. -/
theorem interpolatedPath_mem_through_inner_boundary (hH : H.IsCellConfiguration)
    {U V : Set Plane} (hV : IsOpen V) (hVU : V ⊆ U) (hconv : Convex ℝ U)
    (p : H.cells → Plane) (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (ω : ℕ → H.cells)
    (hstart : (((ω 0).1 : Set Plane) ∩ V).Nonempty)
    (hadj : ∀ n, H.Adj (ω n) (ω (n + 1))) (hpos : ∀ K, 0 < H.holding K)
    (hunb : H.JumpTimesUnbounded ω) {n : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ H.jumpTime ω n)
    (havoid : ∀ j < n, ¬ (((ω j).1 : Set Plane) ∩ frontier V).Nonempty)
    (hlast : ((ω n).1 : Set Plane) ⊆ U) : H.interpolatedPath p ω s ∈ U := by
  have hcell : ∀ j ≤ n, ((ω j).1 : Set Plane) ⊆ U := by
    intro j hj
    rcases hj.eq_or_lt with rfl | hj
    · exact hlast
    · exact (cell_subset_before_boundary H hH hV ω hstart hadj
        (fun k hk => havoid k (lt_of_le_of_lt hk hj))).trans hVU
  obtain ⟨j, hj1, hj2⟩ := H.exists_mem_Ico hpos hunb hs
  have hjn : j ≤ n := by
    by_contra h
    have hmono := (H.jumpTime_strictMono (ω := ω) hpos) (Nat.lt_of_not_ge h)
    exact (not_lt_of_ge (hj1.trans hst)) hmono
  by_cases hj : j = n
  · subst j
    have heq : s = H.jumpTime ω n := le_antisymm hst hj1
    rw [heq, H.interpolatedPath_eq_lineMap hpos le_rfl
      (H.jumpTime_strictMono (ω := ω) hpos (Nat.lt_succ_self n)).le]
    simpa using hcell n le_rfl (hp (ω n))
  · have hjlt : j < n := lt_of_le_of_ne hjn hj
    have hd : 0 < H.jumpTime ω (j + 1) - H.jumpTime ω j := by
      rw [H.jumpTime_succ]
      simpa using hpos (ω j)
    rw [H.interpolatedPath_eq_lineMap hpos hj1 hj2.le]
    apply hconv.lineMap_mem (hcell j hjn (hp _)) (hcell (j + 1) (Nat.succ_le_of_lt hjlt) (hp _))
    exact ⟨div_nonneg (sub_nonneg.mpr hj1) hd.le,
      (div_le_one hd).2 (sub_le_sub_right hj2.le _)⟩

end LatticeProb.CellConfigBoundary

end
