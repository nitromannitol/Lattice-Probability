import LatticeProb.Prob.Percolation.InfiniteComponentDeletion
import LatticeProb.Prob.Percolation.LatticeBondTranslationLaw

/-!
# Deleting the horizontal unit bond in the fully open plane

A nonempty singleton flip removes the horizontal unit edge while retaining a three-edge
route around its unit square. Thus the flipped graph is connected, has a unique infinite
component, and retains the entire selected source support.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open LatticeProb.Graph.Zd

/-- The nonempty horizontal singleton flip has exactly the literal deletion graph. -/
theorem allOpen_flip_horizontal_eq_deleteEdges :
    openGraph (finiteBondFlip {horizontalUnitBond} (allOpen 2)) =
      (nearestNeighborGraph 2).deleteEdges {s(0, unit (0 : Fin 2))} := by
  rw [openGraph_finiteBondFlip_eq_deleteEdges_of_all_open
    {horizontalUnitBond} (allOpen 2) (fun _ _ => rfl),
    openGraph_allOpen]
  congr 1
  simp only [deletedBondEdges, Finset.coe_singleton, Set.image_singleton,
    horizontalUnitBond, bondOfAdjacent]

/-- The selected horizontal edge changes from open to closed under this nonempty flip. -/
theorem allOpen_flip_horizontal_not_adj :
    ¬ (openGraph (finiteBondFlip {horizontalUnitBond} (allOpen 2))).Adj
      0 (unit (0 : Fin 2)) := by
  rw [allOpen_flip_horizontal_eq_deleteEdges, SimpleGraph.deleteEdges_adj]
  exact fun h => h.2 (Set.mem_singleton _)

private theorem square_edge_survives {x y : Vertex 2}
    (h : (nearestNeighborGraph 2).Adj x y)
    (hne : s(x, y) ≠ s(0, unit (0 : Fin 2))) :
    (openGraph (finiteBondFlip {horizontalUnitBond} (allOpen 2))).Adj x y := by
  rw [allOpen_flip_horizontal_eq_deleteEdges, SimpleGraph.deleteEdges_adj]
  exact ⟨h, hne⟩

/-- The vertical unit edge survives the horizontal singleton flip. -/
theorem allOpen_flip_horizontal_vertical_adj :
    (openGraph (finiteBondFlip {horizontalUnitBond} (allOpen 2))).Adj
      0 (unit (1 : Fin 2)) := by
  apply square_edge_survives ⟨1, Or.inl (zero_add _).symm⟩
  decide

/-- The three other sides of the unit square give an actual route around the deleted edge. -/
theorem allOpen_flip_horizontal_detour :
    (openGraph (finiteBondFlip {horizontalUnitBond} (allOpen 2))).Reachable
      0 (unit (0 : Fin 2)) := by
  have htop : (openGraph (finiteBondFlip {horizontalUnitBond} (allOpen 2))).Adj
      (unit (1 : Fin 2)) (unit (1 : Fin 2) + unit (0 : Fin 2)) := by
    apply square_edge_survives ⟨0, Or.inl rfl⟩
    decide
  have hright : (openGraph (finiteBondFlip {horizontalUnitBond} (allOpen 2))).Adj
      (unit (1 : Fin 2) + unit (0 : Fin 2)) (unit (0 : Fin 2)) := by
    apply square_edge_survives ⟨1, Or.inr (add_comm _ _)⟩
    decide
  exact allOpen_flip_horizontal_vertical_adj.reachable.trans
    (htop.reachable.trans hright.reachable)

/-- The square detour discharges nonbridgeness, so deleting the edge preserves connectedness. -/
theorem allOpen_flip_horizontal_connected :
    (openGraph (finiteBondFlip {horizontalUnitBond} (allOpen 2))).Connected := by
  rw [allOpen_flip_horizontal_eq_deleteEdges]
  apply (latticeConnected 2).connected_delete_edge_of_not_isBridge
  rw [SimpleGraph.isBridge_iff]
  exact not_not.mpr (by
    rw [← allOpen_flip_horizontal_eq_deleteEdges]
    exact allOpen_flip_horizontal_detour)

/-- Connectedness of the flipped plane and infinitude of its vertex set give unique infinitude. -/
theorem allOpen_flip_horizontal_hasUniqueInfiniteOpenComponent :
    HasUniqueInfiniteOpenComponent (finiteBondFlip {horizontalUnitBond} (allOpen 2)) := by
  let G := openGraph (finiteBondFlip {horizontalUnitBond} (allOpen 2))
  have hsupp : (G.connectedComponentMk 0).supp = Set.univ := by
    ext x
    exact iff_true_intro (SimpleGraph.ConnectedComponent.sound
      (allOpen_flip_horizontal_connected.preconnected x 0))
  refine ⟨G.connectedComponentMk 0, ?_, ?_⟩
  · change (G.connectedComponentMk 0).supp.Infinite
    rw [hsupp]
    exact Set.infinite_univ
  · intro C _
    obtain ⟨x, hx⟩ := C.nonempty_supp
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff C x).mp hx |>.symm.trans
      (SimpleGraph.ConnectedComponent.sound
        (allOpen_flip_horizontal_connected.preconnected x 0))

/-- The nonempty deletion has exactly the old actual unique infinite support. -/
theorem allOpen_flip_horizontal_uniqueInfiniteComponent_supp :
    (uniqueInfiniteComponent allOpen_flip_horizontal_hasUniqueInfiniteOpenComponent).supp =
      (uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)).supp := by
  apply uniqueInfiniteComponent_supp_eq_of_finiteBondFlip_of_retained_connected
    {horizontalUnitBond} (allOpen_hasUniqueInfiniteOpenComponent 2)
    allOpen_flip_horizontal_hasUniqueInfiniteOpenComponent (fun _ _ => rfl)
  intro x _ y _
  exact allOpen_flip_horizontal_connected.preconnected x y

end LatticeProb.Percolation
