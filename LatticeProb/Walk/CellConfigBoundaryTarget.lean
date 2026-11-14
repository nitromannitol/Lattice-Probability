import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingValid

/-!
# Compact sets of cells

A compact set meets finitely many cells of a locally finite configuration, and a
nonempty set meets at least one cell when the cells cover the plane.
-/

set_option autoImplicit false

open Set
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigBoundary

variable (H : CellConfig)

/-- A compact set meets only finitely many cells of a cell configuration. -/
theorem finite_cells_meeting (hH : H.IsCellConfiguration) {A : Set Plane}
    (hA : IsCompact A) : {K : H.cells | ((K.1 : Set Plane) ∩ A).Nonempty}.Finite := by
  exact ((CellConfig.finite_restrict_of_isCompact hH hA).preimage
    Subtype.val_injective.injOn).subset (fun K hK => ⟨K.2, hK⟩)

/-- A nonempty set meets at least one cell. -/
theorem nonempty_cells_meeting (hH : H.IsCellConfiguration) {A : Set Plane}
    (hA : A.Nonempty) : {K : H.cells | ((K.1 : Set Plane) ∩ A).Nonempty}.Nonempty := by
  obtain ⟨z, hz⟩ := hA
  have hz' : z ∈ ⋃ K ∈ H.cells, (K : Set Plane) := by rw [hH.iUnion_eq_univ]; trivial
  obtain ⟨K, hK, hzK⟩ := mem_iUnion₂.mp hz'
  exact ⟨⟨K, hK⟩, z, hzK, hz⟩

/-- The cells meeting a compact nonempty frontier form a finite nonempty set. -/
theorem finite_nonempty_cells_meeting_frontier (hH : H.IsCellConfiguration) {U : Set Plane}
    (hc : IsCompact (frontier U)) (hne : (frontier U).Nonempty) :
    {K : H.cells | ((K.1 : Set Plane) ∩ frontier U).Nonempty}.Finite ∧
      {K : H.cells | ((K.1 : Set Plane) ∩ frontier U).Nonempty}.Nonempty :=
  ⟨finite_cells_meeting H hH hc, nonempty_cells_meeting H hH hne⟩


/-- The boundary cells of a nonempty bounded domain are finite and nonempty. -/
theorem finite_nonempty_cells_meeting_frontier_of_bounded (hH : H.IsCellConfiguration)
    {U : Set Plane} (hb : Bornology.IsBounded U) (hne : U.Nonempty) :
    {K : H.cells | ((K.1 : Set Plane) ∩ frontier U).Nonempty}.Finite ∧
      {K : H.cells | ((K.1 : Set Plane) ∩ frontier U).Nonempty}.Nonempty := by
  apply finite_nonempty_cells_meeting_frontier H hH
  · exact hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  · apply nonempty_frontier_iff.mpr
    refine ⟨hne, ?_⟩
    intro heq
    exact NormedSpace.unbounded_univ ℝ Plane (heq ▸ hb)

end LatticeProb.CellConfigBoundary
