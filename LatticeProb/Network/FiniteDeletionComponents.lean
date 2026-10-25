import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Set.Finite.Lattice

/-!
# Finite exceptions after finite edge deletion

Deleting finitely many edges from a connected graph leaves only finitely many vertices
outside any unique infinite component. The proof finds a deleted-edge endpoint in each
other component by following a walk in the original graph. No local finiteness is needed.
-/

namespace LatticeProb.Network

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {B : Set (Sym2 V)}

/-- A walk leaving a component of the deleted graph crosses a deleted edge from that
component. The endpoint in the component is retained as an explicit witness. -/
theorem exists_deleted_edge_of_walk {u v : V} (p : G.Walk u v)
    (C : (G.deleteEdges B).ConnectedComponent) (hu : u ∈ C.supp) (hv : v ∉ C.supp) :
    ∃ x ∈ C.supp, ∃ y, G.Adj x y ∧ s(x, y) ∈ B := by
  classical
  induction p with
  | nil => exact (hv hu).elim
  | @cons u w v huw p ih =>
    by_cases hb : s(u, w) ∈ B
    · exact ⟨u, hu, w, huw, hb⟩
    · have hdel : (G.deleteEdges B).Adj u w := deleteEdges_adj.mpr ⟨huw, hb⟩
      exact ih ((C.mem_supp_congr_adj hdel).mp hu) hv

/-- In a connected graph, every component distinct from a specified component after edge
removal contains an endpoint of an actually removed edge. -/
theorem component_contains_deleted_endpoint (hG : G.Connected)
    (K C : (G.deleteEdges B).ConnectedComponent) (hCK : C ≠ K) :
    ∃ x ∈ C.supp, ∃ y, G.Adj x y ∧ s(x, y) ∈ B := by
  obtain ⟨u, hu⟩ := C.nonempty_supp
  obtain ⟨v, hv⟩ := K.nonempty_supp
  have hvC : v ∉ C.supp := fun h => hCK (ConnectedComponent.eq_of_common_vertex h hv)
  obtain ⟨p⟩ := hG.preconnected u v
  exact exists_deleted_edge_of_walk p C hu hvC

/-- If deleting a finite unordered edge set from a connected graph leaves a unique infinite
component, its complement is finite. Uniqueness concerns the actual component supports. -/
theorem finite_compl_of_unique_infinite_component (hG : G.Connected) (hB : B.Finite)
    (K : (G.deleteEdges B).ConnectedComponent) (_hK : K.supp.Infinite)
    (hunique : ∀ C : (G.deleteEdges B).ConnectedComponent, C.supp.Infinite → C = K) :
    K.suppᶜ.Finite := by
  classical
  let S : Set V := ⋃ e ∈ B, (e.toFinset : Set V)
  have hS : S.Finite := hB.biUnion fun e _ => e.toFinset.finite_toSet
  let T := (G.deleteEdges B).connectedComponentMk '' (S \ K.supp)
  have hT : T.Finite := (hS.subset Set.sdiff_subset).image _
  have hfinite : ∀ C ∈ T, C.supp.Finite := by
    rintro C ⟨x, hx, rfl⟩
    by_contra hinf
    have heq := hunique _ hinf
    exact hx.2 ((ConnectedComponent.mem_supp_iff K x).mpr heq)
  have hcover : K.suppᶜ ⊆ ⋃ C ∈ T, C.supp := by
    intro x hx
    let C := (G.deleteEdges B).connectedComponentMk x
    have hxC : x ∈ C.supp := (ConnectedComponent.mem_supp_iff C x).mpr rfl
    have hCK : C ≠ K := fun h => hx ((ConnectedComponent.mem_supp_iff K x).mpr h)
    obtain ⟨y, hy, z, _, hyz⟩ := component_contains_deleted_endpoint hG K C hCK
    have hyS : y ∈ S := Set.mem_iUnion.mpr ⟨s(y, z),
      Set.mem_iUnion.mpr ⟨hyz, Sym2.mem_toFinset.mpr (Sym2.mem_iff.mpr (Or.inl rfl))⟩⟩
    have hyK : y ∉ K.supp := fun h => hCK (ConnectedComponent.eq_of_common_vertex hy h)
    have hCT : C ∈ T := ⟨y, ⟨hyS, hyK⟩, (ConnectedComponent.mem_supp_iff C y).mp hy⟩
    exact Set.mem_iUnion.mpr ⟨C, Set.mem_iUnion.mpr ⟨hCT, hxC⟩⟩
  exact (hT.biUnion hfinite).subset hcover

end LatticeProb.Network
