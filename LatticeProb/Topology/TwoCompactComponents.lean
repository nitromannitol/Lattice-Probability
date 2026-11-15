import LatticeProb.Topology.CompactComponentSeparation
import LatticeProb.Topology.CompactComponentWitness

/-! # Separating two non-singleton components of a compact set -/

set_option autoImplicit false

open Set TopologicalSpace

namespace LatticeProb.Topology

private theorem component_subset_left {X : Type*} [TopologicalSpace X] [T2Space X]
    {S A B : Set X} {x : X} (hA : IsCompact A) (hB : IsCompact B)
    (hAB : Disjoint A B) (hU : A ∪ B = S) (hx : x ∈ A) :
    connectedComponentIn S x ⊆ A := by
  have hxS : x ∈ S := hU ▸ mem_union_left B hx
  have hsub : connectedComponentIn S x ⊆ A ∪ B := by
    rw [hU]
    exact connectedComponentIn_subset S x
  have hdis : connectedComponentIn S x ∩ (A ∩ B) = ∅ := by
    rw [disjoint_iff_inter_eq_empty.mp hAB, inter_empty]
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp
      isPreconnected_connectedComponentIn A B hA.isClosed hB.isClosed hsub hdis with h | h
  · exact h
  · exact False.elim (disjoint_left.mp hAB hx (h (mem_connectedComponentIn hxS)))

private theorem component_compact {X : Type*} [TopologicalSpace X] [T2Space X]
    {S : Set X} (hS : IsCompact S) (x : X) (hx : x ∈ S) :
    IsCompact (connectedComponentIn S x) := by
  have hc : IsClosed (connectedComponentIn S x) := by
    apply closure_subset_iff_isClosed.mp
    apply IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn.closure
    · exact subset_closure (mem_connectedComponentIn hx)
    · exact closure_minimal (connectedComponentIn_subset S x) hS.isClosed
  exact hS.of_isClosed_subset hc (connectedComponentIn_subset S x)

/-- A compact set has two distinct non-singleton components exactly when it
has a disjoint compact partition with a non-singleton connected compact subset
on each side. -/
theorem two_nonsubsingleton_components_iff_compact_partition
    {X : Type*} [TopologicalSpace X] [T2Space X] {S : Set X} (hS : IsCompact S) :
    (∃ x ∈ S, ∃ y ∈ S,
      connectedComponentIn S x ≠ connectedComponentIn S y ∧
      ¬ (connectedComponentIn S x).Subsingleton ∧
      ¬ (connectedComponentIn S y).Subsingleton) ↔
    ∃ A B : Set X, IsCompact A ∧ IsCompact B ∧ Disjoint A B ∧ A ∪ B = S ∧
      (∃ K : Set X, IsCompact K ∧ IsConnected K ∧ K ⊆ A ∧ ¬ K.Subsingleton) ∧
      (∃ K : Set X, IsCompact K ∧ IsConnected K ∧ K ⊆ B ∧ ¬ K.Subsingleton) := by
  constructor
  · rintro ⟨x, hx, y, hy, hne, hnx, hny⟩
    have hxy : y ∉ connectedComponentIn S x := fun h => hne (connectedComponentIn_eq h)
    obtain ⟨A, B, hA, hB, hAB, hU, hxA, hyB⟩ :=
      (not_mem_component_iff_compact_partition hS hx hy).mp hxy
    have hCx := component_subset_left hA hB hAB hU hxA
    have hCy := component_subset_left hB hA hAB.symm (union_comm A B ▸ hU) hyB
    exact ⟨A, B, hA, hB, hAB, hU,
      ⟨_, component_compact hS x hx, isConnected_connectedComponentIn_iff.mpr hx, hCx, hnx⟩,
      ⟨_, component_compact hS y hy, isConnected_connectedComponentIn_iff.mpr hy, hCy, hny⟩⟩
  · rintro ⟨A, B, hA, hB, hAB, hU, ⟨K, _, hK, hKA, hnK⟩,
      ⟨L, _, hL, hLB, hnL⟩⟩
    obtain ⟨x, hxK⟩ := hK.nonempty
    obtain ⟨y, hyL⟩ := hL.nonempty
    have hxA := hKA hxK
    have hyB := hLB hyL
    have hxS : x ∈ S := hU ▸ mem_union_left B hxA
    have hyS : y ∈ S := hU ▸ mem_union_right A hyB
    have hKsub : K ⊆ connectedComponentIn S x :=
      hK.isPreconnected.subset_connectedComponentIn hxK (hKA.trans (hU ▸ subset_union_left))
    have hLsub : L ⊆ connectedComponentIn S y :=
      hL.isPreconnected.subset_connectedComponentIn hyL (hLB.trans (hU ▸ subset_union_right))
    refine ⟨x, hxS, y, hyS, ?_, fun h => hnK (h.anti hKsub), fun h => hnL (h.anti hLsub)⟩
    intro heq
    have hyC : y ∈ connectedComponentIn S x := heq ▸ mem_connectedComponentIn hyS
    exact disjoint_left.mp hAB (component_subset_left hA hB hAB hU hxA hyC) hyB

end LatticeProb.Topology
