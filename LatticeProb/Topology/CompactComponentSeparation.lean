import LatticeProb.Topology.CompactSplit

/-! # Separation of components of compact sets -/

set_option autoImplicit false

open Set TopologicalSpace

namespace LatticeProb.Topology

/-- Two points of a compact Hausdorff set lie in different components exactly
when they can be separated by a disjoint compact partition of the set. -/
theorem not_mem_component_iff_compact_partition
    {X : Type*} [TopologicalSpace X] [T2Space X] {S : Set X}
    (hS : IsCompact S) {x y : X} (hx : x ∈ S) (hy : y ∈ S) :
    y ∉ connectedComponentIn S x ↔
      ∃ A B : Set X, IsCompact A ∧ IsCompact B ∧ Disjoint A B ∧
        A ∪ B = S ∧ x ∈ A ∧ y ∈ B := by
  constructor
  · intro hxy
    have hsep : ∀ T ⊆ S, IsPreconnected T →
        ¬ ((T ∩ {x}).Nonempty ∧ (T ∩ {y}).Nonempty) := by
      intro T hTS hT h
      obtain ⟨⟨a, haT, hax⟩, ⟨b, hbT, hby⟩⟩ := h
      have hxT : x ∈ T := by simpa only [mem_singleton_iff] using hax ▸ haT
      have hyT : y ∈ T := by simpa only [mem_singleton_iff] using hby ▸ hbT
      exact hxy (hT.subset_connectedComponentIn hxT hTS hyT)
    obtain ⟨A, B, hA, hB, hAB, hU, hAy, hBx⟩ :=
      exists_compact_split hS isClosed_singleton isClosed_singleton hsep
    have hxAB : x ∈ A ∪ B := hU.symm ▸ hx
    have hyAB : y ∈ A ∪ B := hU.symm ▸ hy
    have hxA : x ∈ A := hxAB.resolve_right (fun h =>
      disjoint_left.mp hBx h (mem_singleton x))
    have hyB : y ∈ B := hyAB.resolve_left (fun h =>
      disjoint_left.mp hAy h (mem_singleton y))
    exact ⟨A, B, hA, hB, hAB, hU, hxA, hyB⟩
  · rintro ⟨A, B, hA, hB, hAB, hU, hxA, hyB⟩ hyC
    have hCsub : connectedComponentIn S x ⊆ A ∪ B := by
      rw [hU]
      exact connectedComponentIn_subset S x
    have hCdis : connectedComponentIn S x ∩ (A ∩ B) = ∅ := by
      rw [disjoint_iff_inter_eq_empty.mp hAB, inter_empty]
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp
      isPreconnected_connectedComponentIn A B hA.isClosed hB.isClosed hCsub hCdis with hCA | hCB
    · exact disjoint_left.mp hAB (hCA hyC) hyB
    · exact disjoint_left.mp hAB hxA (hCB (mem_connectedComponentIn hx))

end LatticeProb.Topology
