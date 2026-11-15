import LatticeProb.Topology.CompactComponentSeparation

/-! # Separation of finitely many components of a compact set -/

set_option autoImplicit false

open Set TopologicalSpace

namespace LatticeProb.Topology

/-- A point of a compact Hausdorff set can be separated by a compact
partition from finitely many points outside its connected component. -/
theorem exists_compact_partition_separating_finite
    {X : Type*} [TopologicalSpace X] [T2Space X] {S : Set X}
    (hS : IsCompact S) {x : X} (hx : x ∈ S) (t : Finset X)
    (htS : ∀ y ∈ t, y ∈ S)
    (ht : ∀ y ∈ t, y ∉ connectedComponentIn S x) :
    ∃ A B : Set X, IsCompact A ∧ IsCompact B ∧ Disjoint A B ∧
      A ∪ B = S ∧ x ∈ A ∧ ∀ y ∈ t, y ∈ B := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    exact ⟨S, ∅, hS, isCompact_empty, disjoint_empty S, union_empty S, hx,
      by intro y hy; exact False.elim (Finset.notMem_empty y hy)⟩
  | @insert y t hyt ih =>
    have hyS : y ∈ S := htS y (Finset.mem_insert_self y t)
    have hy : y ∉ connectedComponentIn S x := ht y (Finset.mem_insert_self y t)
    obtain ⟨A, B, hA, hB, hAB, hU, hxA, htB⟩ :=
      ih (fun z hz => htS z (Finset.mem_insert_of_mem hz))
        (fun z hz => ht z (Finset.mem_insert_of_mem hz))
    obtain ⟨C, D, hC, hD, hCD, hV, hxC, hyD⟩ :=
      (not_mem_component_iff_compact_partition hS hx hyS).mp hy
    refine ⟨A ∩ C, B ∪ D, hA.inter_right hC.isClosed, hB.union hD, ?_, ?_,
      ⟨hxA, hxC⟩, ?_⟩
    · rw [disjoint_left]
      intro z hz hw
      rcases hw with hzB | hzD
      · exact disjoint_left.mp hAB hz.1 hzB
      · exact disjoint_left.mp hCD hz.2 hzD
    · ext z
      have hu : z ∈ A ∨ z ∈ B ↔ z ∈ S := by
        simpa only [mem_union] using Iff.of_eq (congrArg (z ∈ ·) hU)
      have hv : z ∈ C ∨ z ∈ D ↔ z ∈ S := by
        simpa only [mem_union] using Iff.of_eq (congrArg (z ∈ ·) hV)
      simp only [mem_union, mem_inter_iff]
      tauto
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Or.inr hyD
      · exact Or.inl (htB z hz)

end LatticeProb.Topology
