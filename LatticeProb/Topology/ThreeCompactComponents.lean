import LatticeProb.Topology.ThreeCompactComponentSeparation

/-! # Three non-singleton components of a compact set -/

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

private theorem component_subset_piece {X : Type*} [TopologicalSpace X] [T2Space X]
    {S A B C : Set X} {x : X} (hA : IsCompact A) (hB : IsCompact B)
    (hC : IsCompact C) (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hU : A ∪ B ∪ C = S) (hx : x ∈ A) :
    connectedComponentIn S x ⊆ A := by
  apply component_subset_left hA (hB.union hC) (disjoint_union_right.mpr ⟨hAB, hAC⟩) _ hx
  rw [← union_assoc]
  exact hU

/-- Three distinct non-singleton components of a compact set are equivalent to
three disjoint compact partition pieces each containing a connected compact
non-singleton subset. -/
theorem three_nonsubsingleton_components_iff_compact_partition
    {X : Type*} [TopologicalSpace X] [T2Space X] {S : Set X} (hS : IsCompact S) :
    (∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S,
      connectedComponentIn S x ≠ connectedComponentIn S y ∧
      connectedComponentIn S x ≠ connectedComponentIn S z ∧
      connectedComponentIn S y ≠ connectedComponentIn S z ∧
      ¬ (connectedComponentIn S x).Subsingleton ∧
      ¬ (connectedComponentIn S y).Subsingleton ∧
      ¬ (connectedComponentIn S z).Subsingleton) ↔
    ∃ A B C : Set X, IsCompact A ∧ IsCompact B ∧ IsCompact C ∧
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧ A ∪ B ∪ C = S ∧
      (∃ K : Set X, IsCompact K ∧ IsConnected K ∧ K ⊆ A ∧ ¬ K.Subsingleton) ∧
      (∃ K : Set X, IsCompact K ∧ IsConnected K ∧ K ⊆ B ∧ ¬ K.Subsingleton) ∧
      (∃ K : Set X, IsCompact K ∧ IsConnected K ∧ K ⊆ C ∧ ¬ K.Subsingleton) := by
  constructor
  · rintro ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, hnx, hny, hnz⟩
    obtain ⟨A, B, C, hA, hB, hC, hAB, hAC, hBC, hU, hxA, hyB, hzC⟩ :=
      exists_compact_partition_three_components hS hx hy hz hxy hxz hyz
    have hU' : B ∪ A ∪ C = S := by simpa only [union_comm B A] using hU
    have hU'' : C ∪ A ∪ B = S := by
      calc
        C ∪ A ∪ B = A ∪ B ∪ C := by ext p; simp only [mem_union]; tauto
        _ = S := hU
    have hCx := component_subset_piece hA hB hC hAB hAC hU hxA
    have hCy := component_subset_piece hB hA hC hAB.symm hBC hU' hyB
    have hCz := component_subset_piece hC hA hB hAC.symm hBC.symm hU'' hzC
    exact ⟨A, B, C, hA, hB, hC, hAB, hAC, hBC, hU,
      ⟨_, component_compact hS x hx, isConnected_connectedComponentIn_iff.mpr hx, hCx, hnx⟩,
      ⟨_, component_compact hS y hy, isConnected_connectedComponentIn_iff.mpr hy, hCy, hny⟩,
      ⟨_, component_compact hS z hz, isConnected_connectedComponentIn_iff.mpr hz, hCz, hnz⟩⟩
  · rintro ⟨A, B, C, hA, hB, hC, hAB, hAC, hBC, hU,
      ⟨K, _, hK, hKA, hnK⟩, ⟨L, _, hL, hLB, hnL⟩, ⟨M, _, hM, hMC, hnM⟩⟩
    obtain ⟨x, hxK⟩ := hK.nonempty
    obtain ⟨y, hyL⟩ := hL.nonempty
    obtain ⟨z, hzM⟩ := hM.nonempty
    have hxA := hKA hxK
    have hyB := hLB hyL
    have hzC := hMC hzM
    have hAS : A ⊆ S := hU ▸ (subset_union_left.trans subset_union_left)
    have hBS : B ⊆ S := hU ▸ (subset_union_right.trans subset_union_left)
    have hCS : C ⊆ S := hU ▸ subset_union_right
    have hxS := hAS hxA
    have hyS := hBS hyB
    have hzS := hCS hzC
    have hKsub : K ⊆ connectedComponentIn S x :=
      hK.isPreconnected.subset_connectedComponentIn hxK (hKA.trans hAS)
    have hLsub : L ⊆ connectedComponentIn S y :=
      hL.isPreconnected.subset_connectedComponentIn hyL (hLB.trans hBS)
    have hMsub : M ⊆ connectedComponentIn S z :=
      hM.isPreconnected.subset_connectedComponentIn hzM (hMC.trans hCS)
    have hU' : B ∪ A ∪ C = S := by simpa only [union_comm B A] using hU
    have hCx := component_subset_piece hA hB hC hAB hAC hU hxA
    have hCy := component_subset_piece hB hA hC hAB.symm hBC hU' hyB
    refine ⟨x, hxS, y, hyS, z, hzS, ?_, ?_, ?_,
      fun h => hnK (h.anti hKsub), fun h => hnL (h.anti hLsub), fun h => hnM (h.anti hMsub)⟩
    · intro heq
      exact disjoint_left.mp hAB (hCx (heq ▸ mem_connectedComponentIn hyS)) hyB
    · intro heq
      exact disjoint_left.mp hAC (hCx (heq ▸ mem_connectedComponentIn hzS)) hzC
    · intro heq
      exact disjoint_left.mp hBC (hCy (heq ▸ mem_connectedComponentIn hzS)) hzC

end LatticeProb.Topology
