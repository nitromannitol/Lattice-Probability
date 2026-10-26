import LatticeProb.Prob.Percolation.OpenComponentTranslation
import LatticeProb.Prob.Percolation.LatticeClusterBall
import LatticeProb.Prob.Percolation.LatticeBondTranslationLaw

/-!
# Nonidentity translation of closed and open components

The origin component in the closed two-dimensional lattice moves to the singleton vertical
unit vertex. The infinite origin component in the open lattice stays infinite, with both the
translated root and the origin belonging to its support.
-/

namespace LatticeProb.Percolation

/-- The actual all-closed origin component translates to exactly the vertical unit singleton. -/
theorem allClosed_origin_componentTranslation_supp :
    (openComponentTranslation (unit (1 : Fin 2)) (allClosed 2)
      ((openGraph (allClosed 2)).connectedComponentMk 0)).supp =
        {unit (1 : Fin 2)} := by
  have hs : ((openGraph (allClosed 2)).connectedComponentMk 0).supp = {0} := by
    ext x
    constructor
    · intro hx
      exact allClosed_component_vertex_eq 0 ⟨x, hx⟩
    · intro hx
      have hx0 : x = 0 := hx
      subst x
      rfl
  rw [openComponentTranslation_supp, hs, Set.image_singleton, zero_add]

/-- The closed consumer contains the moved root and excludes its original root. -/
theorem allClosed_origin_componentTranslation_membership :
    let C := openComponentTranslation (unit (1 : Fin 2)) (allClosed 2)
      ((openGraph (allClosed 2)).connectedComponentMk 0)
    unit (1 : Fin 2) ∈ C.supp ∧ (0 : Vertex 2) ∉ C.supp := by
  dsimp only
  rw [allClosed_origin_componentTranslation_supp]
  exact ⟨rfl, fun h => verticalUnit_ne_zero h.symm⟩

/-- The actual all-open origin component remains infinite and contains the unit and origin. -/
theorem allOpen_origin_componentTranslation_infinite_membership :
    let C := openComponentTranslation (unit (1 : Fin 2)) (allOpen 2)
      ((openGraph (allOpen 2)).connectedComponentMk 0)
    C.supp.Infinite ∧ unit (1 : Fin 2) ∈ C.supp ∧ (0 : Vertex 2) ∈ C.supp := by
  dsimp only
  refine ⟨(openComponentTranslation_infinite_iff _ _).mpr
    (allOpen_mem_infiniteComponentEvent 0), ?_, ?_⟩
  · have hroot := (add_mem_openComponentTranslation_supp (unit (1 : Fin 2))
      ((openGraph (allOpen 2)).connectedComponentMk 0) 0).mpr rfl
    simpa only [zero_add] using hroot
  · rw [mem_openComponentTranslation_supp, SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq, openGraph_allOpen]
    exact (Graph.Zd.latticeConnected 2).preconnected _ _

end LatticeProb.Percolation
