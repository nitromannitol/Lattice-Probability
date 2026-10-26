import LatticeProb.Prob.Percolation.DeletedInfiniteComponent
import LatticeProb.Prob.Percolation.FiniteBondDeletionConsumer

/-!
# Actual induced infinite component after a horizontal singleton deletion

The fully open plane and its nonempty horizontal singleton deletion discharge all
uniqueness and openness hypotheses. Every actual old component vertex has an infinite
induced component with full support and the exact ambient-support preimage.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

/-- Nonempty horizontal deletion has unique infinitude on the actual old infinite carrier. -/
theorem allOpen_flip_horizontal_induce_existsUnique_infinite_component :
    ∃! E : ((openGraph (finiteBondFlip {horizontalUnitBond} (allOpen 2))).induce
      (uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)).supp).ConnectedComponent,
      E.supp.Infinite := by
  exact finiteBondFlip_induce_existsUnique_infinite_component {horizontalUnitBond}
    (allOpen_hasUniqueInfiniteOpenComponent 2)
    allOpen_flip_horizontal_hasUniqueInfiniteOpenComponent (fun _ _ => rfl)

/-- Every actual subtype vertex has infinite full induced support and exact ambient preimage. -/
theorem allOpen_flip_horizontal_induce_component_supp
    (x : uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)) :
    let H := openGraph (finiteBondFlip {horizontalUnitBond} (allOpen 2))
    let C := uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)
    ((H.induce C.supp).connectedComponentMk x).supp =
        Subtype.val ⁻¹'
          (uniqueInfiniteComponent allOpen_flip_horizontal_hasUniqueInfiniteOpenComponent).supp ∧
      ((H.induce C.supp).connectedComponentMk
        x).supp = Set.univ ∧
      ((H.induce C.supp).connectedComponentMk
        x).supp.Infinite := by
  dsimp only
  have hx : x.val ∈
      (uniqueInfiniteComponent allOpen_flip_horizontal_hasUniqueInfiniteOpenComponent).supp := by
    rw [allOpen_flip_horizontal_uniqueInfiniteComponent_supp]
    exact x.property
  have heq := finiteBondFlip_induce_infinite_component_supp {horizontalUnitBond}
    (allOpen_hasUniqueInfiniteOpenComponent 2)
    allOpen_flip_horizontal_hasUniqueInfiniteOpenComponent (fun _ _ => rfl) x hx
  refine ⟨heq, ?_, ?_⟩
  · rw [heq, allOpen_flip_horizontal_uniqueInfiniteComponent_supp,
      uniqueInfiniteComponent_allOpen_supp]
    rfl
  · apply (Graph.component_induce_supp_infinite_iff
      (openGraph_finiteBondFlip_le_of_all_open {horizontalUnitBond} (allOpen 2)
        (fun _ _ => rfl)) _ x).mpr
    rw [(SimpleGraph.ConnectedComponent.mem_supp_iff _ x.val).mp hx]
    exact uniqueInfiniteComponent_infinite allOpen_flip_horizontal_hasUniqueInfiniteOpenComponent

/-- The actual origin supplies an inhabited infinite induced component after nonempty deletion. -/
theorem allOpen_flip_horizontal_induce_origin :
    ∃ x : uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2), x.val = 0 ∧
      (((openGraph (finiteBondFlip {horizontalUnitBond} (allOpen 2))).induce
        (uniqueInfiniteComponent
          (allOpen_hasUniqueInfiniteOpenComponent 2)).supp).connectedComponentMk
        x).supp = Set.univ ∧
      (((openGraph (finiteBondFlip {horizontalUnitBond} (allOpen 2))).induce
        (uniqueInfiniteComponent
          (allOpen_hasUniqueInfiniteOpenComponent 2)).supp).connectedComponentMk
        x).supp.Infinite := by
  have hzero : (0 : Vertex 2) ∈
      (uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)).supp := by
    rw [uniqueInfiniteComponent_allOpen_supp]
    trivial
  let x : uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2) := ⟨0, hzero⟩
  exact ⟨x, rfl, (allOpen_flip_horizontal_induce_component_supp x).2⟩

end LatticeProb.Percolation
