import LatticeProb.Topology.CompactComponentSeparation

/-! # Separation of three components of a compact set -/

set_option autoImplicit false

open Set TopologicalSpace

namespace LatticeProb.Topology

/-- Three points in pairwise distinct components of a compact Hausdorff set
belong to three disjoint compact sets whose union is the original set. -/
theorem exists_compact_partition_three_components
    {X : Type*} [TopologicalSpace X] [T2Space X] {S : Set X}
    (hS : IsCompact S) {x y z : X} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hxy : connectedComponentIn S x ≠ connectedComponentIn S y)
    (hxz : connectedComponentIn S x ≠ connectedComponentIn S z)
    (hyz : connectedComponentIn S y ≠ connectedComponentIn S z) :
    ∃ A B C : Set X, IsCompact A ∧ IsCompact B ∧ IsCompact C ∧
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧
      A ∪ B ∪ C = S ∧ x ∈ A ∧ y ∈ B ∧ z ∈ C := by
  have hxy' : y ∉ connectedComponentIn S x := fun h => hxy (connectedComponentIn_eq h)
  have hxz' : z ∉ connectedComponentIn S x := fun h => hxz (connectedComponentIn_eq h)
  have hyz' : z ∉ connectedComponentIn S y := fun h => hyz (connectedComponentIn_eq h)
  obtain ⟨A, B, hA, hB, hAB, hU, hxA, hyB⟩ :=
    (not_mem_component_iff_compact_partition hS hx hy).mp hxy'
  obtain ⟨C, D, hC, hD, hCD, hV, hxC, hzD⟩ :=
    (not_mem_component_iff_compact_partition hS hx hz).mp hxz'
  obtain ⟨E, F, hE, hF, hEF, hW, hyE, hzF⟩ :=
    (not_mem_component_iff_compact_partition hS hy hz).mp hyz'
  refine ⟨A ∩ C, (B ∪ D) ∩ E, (B ∪ D) ∩ F,
    hA.inter_right hC.isClosed, (hB.union hD).inter_right hE.isClosed,
    (hB.union hD).inter_right hF.isClosed, ?_, ?_, ?_, ?_,
    ⟨hxA, hxC⟩, ⟨Or.inl hyB, hyE⟩, ⟨Or.inr hzD, hzF⟩⟩
  · rw [disjoint_left]
    intro p hp hq
    rcases hq.1 with hb | hd
    · exact disjoint_left.mp hAB hp.1 hb
    · exact disjoint_left.mp hCD hp.2 hd
  · rw [disjoint_left]
    intro p hp hq
    rcases hq.1 with hb | hd
    · exact disjoint_left.mp hAB hp.1 hb
    · exact disjoint_left.mp hCD hp.2 hd
  · rw [disjoint_left]
    intro p hp hq
    exact disjoint_left.mp hEF hp.2 hq.2
  · ext p
    have hu : p ∈ A ∨ p ∈ B ↔ p ∈ S := by simpa only [mem_union] using Iff.of_eq (congrArg (p ∈ ·) hU)
    have hv : p ∈ C ∨ p ∈ D ↔ p ∈ S := by simpa only [mem_union] using Iff.of_eq (congrArg (p ∈ ·) hV)
    have hw : p ∈ E ∨ p ∈ F ↔ p ∈ S := by simpa only [mem_union] using Iff.of_eq (congrArg (p ∈ ·) hW)
    simp only [mem_union, mem_inter_iff]
    tauto

end LatticeProb.Topology
