import LatticeProb.Network.EdgeDeletionRigidity

/-!
# Harmonic flux through a bridge with a finite side

The indicator of a deleted component is harmonic on the deleted graph. Its original
Laplacian consists of two opposite endpoint masses. Compact harmonic pairing therefore
forces zero drop when that component is finite. Uniqueness of the infinite deleted
component supplies a finite endpoint side whenever the endpoints are separated.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical

namespace LatticeProb.Network

variable {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]

/-- The indicator of an actual component has zero Laplacian on its own graph. -/
theorem netLaplacian_component_indicator (C : G.ConnectedComponent) (x : V) :
    netLaplacian G (unitCond G) (C.supp.indicator (fun _ => (1 : ℝ))) x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro y hy
  have hxy := (SimpleGraph.mem_neighborFinset G x y).mp hy
  have hm := C.mem_supp_congr_adj hxy
  have he : C.supp.indicator (fun _ => (1 : ℝ)) y =
      C.supp.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ C.supp
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hm.mp hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (hm.not.mp hx)]
  rw [he, sub_self, mul_zero]

/-- The finite-side indicator has original Laplacian minus one at `a`, plus one at `b`.
This formula uses actual deleted reachability and holds even before assuming finiteness. -/
theorem netLaplacian_deleted_component_indicator {a b : V} (hab : G.Adj a b)
    (hsep : ¬ (G.deleteEdges (({s(a, b)} : Finset (Sym2 V)) : Set (Sym2 V))).Reachable a b)
    (x : V) :
    netLaplacian G (unitCond G)
      (((G.deleteEdges
        (({s(a, b)} : Finset (Sym2 V)) : Set (Sym2 V))).connectedComponentMk a).supp.indicator
        (fun _ => (1 : ℝ))) x =
      (if x = a then -1 else 0) + (if x = b then 1 else 0) := by
  classical
  let D := G.deleteEdges (({s(a, b)} : Finset (Sym2 V)) : Set (Sym2 V))
  let C := D.connectedComponentMk a
  have ha : a ∈ C.supp := rfl
  have hb : b ∉ C.supp := by
    intro hb
    exact hsep (C.reachable_of_mem_supp ha hb)
  have hd := netLaplacian_single_edge_difference G hab
    (C.supp.indicator (fun _ => (1 : ℝ))) x
  have hz := netLaplacian_component_indicator D C x
  change netLaplacian G (unitCond G) _ x - netLaplacian D (unitCond D) _ x = _ at hd
  rw [hz, sub_zero, Set.indicator_of_mem ha, Set.indicator_of_notMem hb] at hd
  simpa only [zero_sub, sub_zero] using hd

/-- Finite-side harmonic flux forces the values at the original bridge endpoints to agree. -/
theorem eq_of_harmonic_finite_deleted_component {a b : V} (hab : G.Adj a b)
    (hfin : ((G.deleteEdges
      (({s(a, b)} : Finset (Sym2 V)) : Set (Sym2 V))).connectedComponentMk a).supp.Finite)
    (hsep : ¬ (G.deleteEdges (({s(a, b)} : Finset (Sym2 V)) : Set (Sym2 V))).Reachable a b)
    (u : V → ℝ) (hu : ∀ x, netLaplacian G (unitCond G) u x = 0) : u a = u b := by
  classical
  let C := (G.deleteEdges (({s(a, b)} : Finset (Sym2 V)) : Set (Sym2 V))).connectedComponentMk a
  let B := hfin.toFinset ∪ {b}
  let w := C.supp.indicator (fun _ => (1 : ℝ))
  have hw : ∀ x, x ∉ B → w x = 0 := by
    intro x hx
    apply Set.indicator_of_notMem
    intro h
    exact hx (Finset.mem_union_left _ (hfin.mem_toFinset.mpr h))
  have haB : a ∈ B := Finset.mem_union_left _ (hfin.mem_toFinset.mpr rfl)
  have hbB : b ∈ B := Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have hp := sum_mul_laplacian_eq_zero_of_compact_harmonic G u w B hw hu
  dsimp only [w, C] at hp
  simp_rw [netLaplacian_deleted_component_indicator G hab hsep, mul_add,
    Finset.sum_add_distrib, mul_ite, mul_zero] at hp
  simp only [Finset.sum_ite_eq', if_pos (subset_nbhd B haB),
    if_pos (subset_nbhd B hbB), mul_neg_one, mul_one] at hp
  linarith

omit [G.LocallyFinite] in
/-- Separated endpoints cannot both have infinite components in a graph with a unique
infinite component. The finite side is produced from the actual component supports. -/
theorem finite_endpoint_component_of_unique_infinite (a b : V)
    (hunique : ∃! C : G.ConnectedComponent, C.supp.Infinite)
    (hsep : ¬ G.Reachable a b) :
    (G.connectedComponentMk a).supp.Finite ∨ (G.connectedComponentMk b).supp.Finite := by
  classical
  by_cases ha : (G.connectedComponentMk a).supp.Finite
  · exact Or.inl ha
  · right
    by_contra hb
    obtain ⟨C, _, hC⟩ := hunique
    have heq : G.connectedComponentMk a = G.connectedComponentMk b :=
      (hC _ ha).trans (hC _ hb).symm
    exact hsep (SimpleGraph.ConnectedComponent.exact heq)

/-- A bridge has zero harmonic drop if the deleted graph has a unique infinite component.
No endpoint finiteness, energy or asymptotic comparison is assumed. -/
theorem eq_of_harmonic_unique_infinite_deleted {a b : V} (hab : G.Adj a b)
    (hunique : ∃! C : (G.deleteEdges
      (({s(a, b)} : Finset (Sym2 V)) : Set (Sym2 V))).ConnectedComponent,
      C.supp.Infinite)
    (hsep : ¬ (G.deleteEdges (({s(a, b)} : Finset (Sym2 V)) : Set (Sym2 V))).Reachable a b)
    (u : V → ℝ) (hu : ∀ x, netLaplacian G (unitCond G) u x = 0) : u a = u b := by
  rcases finite_endpoint_component_of_unique_infinite _ a b hunique hsep with ha | hb
  · exact eq_of_harmonic_finite_deleted_component G hab ha hsep u hu
  · have he : (({s(b, a)} : Finset (Sym2 V)) : Set (Sym2 V)) =
        (({s(a, b)} : Finset (Sym2 V)) : Set (Sym2 V)) := by
      rw [Sym2.eq_swap]
    have hb' : ((G.deleteEdges
        (({s(b, a)} : Finset (Sym2 V)) : Set (Sym2 V))).connectedComponentMk b).supp.Finite := by
      rw [he]
      exact hb
    have hs' : ¬ (G.deleteEdges (({s(b, a)} : Finset (Sym2 V)) : Set (Sym2 V))).Reachable b a := by
      rw [he]
      exact fun h => hsep h.symm
    exact (eq_of_harmonic_finite_deleted_component G hab.symm hb' hs' u hu).symm

end LatticeProb.Network
