import LatticeProb.Bonanno.BouRabeeGwynne.FiniteCellSelector

/-! # Initial points in a selected cell -/

set_option autoImplicit false

open Set Metric BouRabeeGwynne

namespace LatticeProb

/-- An active point and every other point in its selected cell lie in the same
inner region, and their distance is bounded by the cell diameter. -/
theorem exists_selected_cell_initial_points
    {X J ι : Type*} [PseudoMetricSpace X]
    (E : ι → Set X) (choice : ι → Option J) (D : Set X) (I : J → Set X)
    (a : ℝ)
    (hactive : ∀ x ∈ D, cellSelector E choice x ≠ none)
    (hdisj : Pairwise (fun k l => Disjoint (E k) (E l)))
    (hinside : ∀ k j, choice k = some j → E k ⊆ I j)
    (hdiam : ∀ k, ∀ x ∈ E k, ∀ y ∈ E k, dist x y ≤ a)
    {x : X} (hx : x ∈ D) :
    ∃ (k : ι) (j : J),
      cellSelector E choice x = some j ∧ choice k = some j ∧ x ∈ E k ∧
      x ∈ I j ∧ ∀ y ∈ E k,
        cellSelector E choice y = some j ∧ y ∈ I j ∧ dist x y ≤ a := by
  cases hs : cellSelector E choice x with
  | none => exact False.elim (hactive x hx hs)
  | some j =>
    obtain ⟨k, hxk, hchoice⟩ := cellSelector_some_mem E choice hs
    refine ⟨k, j, rfl, hchoice, hxk, hinside k j hchoice hxk, ?_⟩
    intro y hy
    exact ⟨(cellSelector_of_label E choice
      ((cellLabel_eq_some_iff E hdisj y k).mpr hy)).trans hchoice,
      hinside k j hchoice hy, hdiam k x hxk y hy⟩

end LatticeProb
