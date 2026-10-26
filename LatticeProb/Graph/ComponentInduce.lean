import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Finite.Basic

/-!
# Restricting a subgraph to an ambient connected component

Walks in a subgraph stay in every ambient component containing their initial vertex.
Restriction therefore preserves actual reachability, component supports, and infinitude.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Graph

variable {V : Type*} {G H : SimpleGraph V}

/-- Restriction to an ambient component preserves subgraph reachability exactly. -/
theorem reachable_induce_component_iff (hHG : H ≤ G) (C : G.ConnectedComponent)
    (x y : C) : (H.induce C.supp).Reachable x y ↔ H.Reachable x.val y.val := by
  constructor
  · exact fun h => h.map (SimpleGraph.Embedding.induce C.supp).toHom
  · rintro ⟨p⟩
    have hlift : ∀ {u v : V} (p : H.Walk u v) (hu : u ∈ C.supp)
        (hv : v ∈ C.supp), (H.induce C.supp).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
      intro u v p
      induction p with
      | nil => intro hu hv; exact SimpleGraph.Reachable.rfl
      | @cons u v w hadj p ih =>
        intro hu hw
        have hv := C.mem_supp_of_adj_mem_supp hu (hHG hadj)
        exact (SimpleGraph.Adj.reachable (G := H.induce C.supp)
          (u := ⟨u, hu⟩) (v := ⟨v, hv⟩) hadj).trans (ih hv hw)
    exact hlift p x.property y.property

/-- Every restricted vertex has precisely the ambient component support preimage. -/
theorem component_induce_supp_eq_preimage (hHG : H ≤ G) (C : G.ConnectedComponent)
    (x : C) : ((H.induce C.supp).connectedComponentMk x).supp =
      Subtype.val ⁻¹' (H.connectedComponentMk x.val).supp := by
  ext y
  exact SimpleGraph.ConnectedComponent.eq.trans
    ((reachable_induce_component_iff hHG C y x).trans
      SimpleGraph.ConnectedComponent.eq.symm)

/-- Subtype inclusion maps the entire restricted support onto the ambient support. -/
theorem component_induce_supp_image (hHG : H ≤ G) (C : G.ConnectedComponent)
    (x : C) : Subtype.val '' ((H.induce C.supp).connectedComponentMk x).supp =
      (H.connectedComponentMk x.val).supp := by
  rw [component_induce_supp_eq_preimage hHG C x]
  apply Set.image_preimage_eq_of_subset
  intro y hy
  exact ⟨⟨y, C.connectedComponentMk_supp_subset_supp hHG x.property hy⟩, rfl⟩

/-- Infinitude transports both ways through the actual injective subtype inclusion. -/
theorem component_induce_supp_infinite_iff (hHG : H ≤ G) (C : G.ConnectedComponent)
    (x : C) : ((H.induce C.supp).connectedComponentMk x).supp.Infinite ↔
      (H.connectedComponentMk x.val).supp.Infinite := by
  rw [← component_induce_supp_image hHG C x]
  exact (Set.infinite_image_iff Subtype.val_injective.injOn).symm

/-- A unique infinite ambient subgraph component contained in `C` remains unique on `C`. -/
theorem existsUnique_infinite_component_induce (hHG : H ≤ G) (C : G.ConnectedComponent)
    (D : H.ConnectedComponent) (hD : D.supp.Infinite)
    (hunique : ∀ E : H.ConnectedComponent, E.supp.Infinite → E = D)
    (hDC : D.supp ⊆ C.supp) :
    ∃! E : (H.induce C.supp).ConnectedComponent, E.supp.Infinite := by
  obtain ⟨x, hx⟩ := D.nonempty_supp
  let z : C := ⟨x, hDC hx⟩
  have hxD : H.connectedComponentMk x = D :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff D x).mp hx
  refine ⟨(H.induce C.supp).connectedComponentMk z, ?_, ?_⟩
  · apply (component_induce_supp_infinite_iff hHG C z).mpr
    change (H.connectedComponentMk x).supp.Infinite
    rw [hxD]
    exact hD
  · intro E hE
    obtain ⟨y, hy⟩ := E.nonempty_supp
    have hyE := (SimpleGraph.ConnectedComponent.mem_supp_iff E y).mp hy
    have hyinf : (H.connectedComponentMk y.val).supp.Infinite := by
      apply (component_induce_supp_infinite_iff hHG C y).mp
      rw [hyE]
      exact hE
    rw [← hyE]
    apply SimpleGraph.ConnectedComponent.sound
    apply (reachable_induce_component_iff hHG C y z).mpr
    exact SimpleGraph.ConnectedComponent.exact ((hunique _ hyinf).trans hxD.symm)

end LatticeProb.Graph
