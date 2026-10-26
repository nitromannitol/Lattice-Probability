import LatticeProb.Graph.ComponentInduce
import LatticeProb.Prob.Percolation.FiniteBondDeletion
import LatticeProb.Prob.Percolation.LatticeUniqueCluster

/-!
# Infinite components after finite open-bond deletion

The new infinite component lies in the old unique infinite component by monotonicity.
Restriction to the old carrier has a unique infinite component even when deletion
separates that carrier. Its support is the literal preimage of the new ambient support.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- Deleting open bonds puts the new infinite component inside the old selected component. -/
theorem finiteBondFlip_uniqueInfiniteComponent_supp_subset (F : Finset (Bond d))
    (hOld : HasUniqueInfiniteOpenComponent ω)
    (hNew : HasUniqueInfiniteOpenComponent (finiteBondFlip F ω))
    (hopen : ∀ e ∈ F, ω e = true) :
    (uniqueInfiniteComponent hNew).supp ⊆ (uniqueInfiniteComponent hOld).supp := by
  obtain ⟨x, hx⟩ := (uniqueInfiniteComponent hNew).nonempty_supp
  have hxD := (SimpleGraph.ConnectedComponent.mem_supp_iff _ x).mp hx
  have hle := openGraph_finiteBondFlip_le_of_all_open F ω hopen
  let E := (openGraph ω).connectedComponentMk x
  have hsub : (uniqueInfiniteComponent hNew).supp ⊆ E.supp := by
    rw [← hxD]
    exact E.connectedComponentMk_supp_subset_supp hle
      ((SimpleGraph.ConnectedComponent.mem_supp_iff E x).mpr rfl)
  have hE : E = uniqueInfiniteComponent hOld :=
    (eq_uniqueInfiniteComponent_iff hOld E).mpr
      ((uniqueInfiniteComponent_infinite hNew).mono hsub)
  exact hE ▸ hsub

/-- The deleted graph on the old actual carrier has a unique infinite actual component. -/
theorem finiteBondFlip_induce_existsUnique_infinite_component (F : Finset (Bond d))
    (hOld : HasUniqueInfiniteOpenComponent ω)
    (hNew : HasUniqueInfiniteOpenComponent (finiteBondFlip F ω))
    (hopen : ∀ e ∈ F, ω e = true) :
    ∃! E : ((openGraph (finiteBondFlip F ω)).induce
      (uniqueInfiniteComponent hOld).supp).ConnectedComponent, E.supp.Infinite := by
  exact Graph.existsUnique_infinite_component_induce
    (openGraph_finiteBondFlip_le_of_all_open F ω hopen) (uniqueInfiniteComponent hOld)
    (uniqueInfiniteComponent hNew) (uniqueInfiniteComponent_infinite hNew)
    (fun E hE => (eq_uniqueInfiniteComponent_iff hNew E).mpr hE)
    (finiteBondFlip_uniqueInfiniteComponent_supp_subset F hOld hNew hopen)

/-- Any old-carrier vertex in the new infinite support identifies its entire induced support. -/
theorem finiteBondFlip_induce_infinite_component_supp (F : Finset (Bond d))
    (hOld : HasUniqueInfiniteOpenComponent ω)
    (hNew : HasUniqueInfiniteOpenComponent (finiteBondFlip F ω))
    (hopen : ∀ e ∈ F, ω e = true) (x : uniqueInfiniteComponent hOld)
    (hx : x.val ∈ (uniqueInfiniteComponent hNew).supp) :
    (((openGraph (finiteBondFlip F ω)).induce
      (uniqueInfiniteComponent hOld).supp).connectedComponentMk x).supp =
      Subtype.val ⁻¹' (uniqueInfiniteComponent hNew).supp := by
  rw [Graph.component_induce_supp_eq_preimage
    (openGraph_finiteBondFlip_le_of_all_open F ω hopen)]
  rw [(SimpleGraph.ConnectedComponent.mem_supp_iff _ x.val).mp hx]

/-- All edges on the full old subtype are deleted by the literal unordered-edge preimage. -/
theorem finiteBondFlip_induce_eq_deleteEdges (F : Finset (Bond d))
    (hopen : ∀ e ∈ F, ω e = true) (C : OpenComponent ω) :
    (openGraph (finiteBondFlip F ω)).induce C.supp =
      (componentGraph C).deleteEdges
        ((Sym2.map (Subtype.val : C → Vertex d)) ⁻¹' deletedBondEdges F) := by
  rw [openGraph_finiteBondFlip_eq_deleteEdges_of_all_open F ω hopen]
  ext x y
  simp only [SimpleGraph.induce_adj, SimpleGraph.deleteEdges_adj, Set.mem_preimage,
    Sym2.map_mk]
  rfl

end LatticeProb.Percolation
