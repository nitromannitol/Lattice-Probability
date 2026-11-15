import LatticeProb.Topology.FiniteCompactComponentPartition

/-! # Finite compact partitions containing components -/

set_option autoImplicit false

open Set TopologicalSpace

namespace LatticeProb.Topology

/-- Finitely many distinct components of a compact Hausdorff set can be
contained in pairwise disjoint compact pieces with a compact residual. -/
theorem exists_compact_partition_containing_finite_components
    {X : Type*} [TopologicalSpace X] [T2Space X] {S : Set X}
    (hS : IsCompact S) (t : Finset X) (htS : ∀ x ∈ t, x ∈ S)
    (ht : ∀ x ∈ t, ∀ y ∈ t, x ≠ y →
      connectedComponentIn S x ≠ connectedComponentIn S y) :
    ∃ (P : X → Set X) (R : Set X),
      IsCompact R ∧ (∀ x ∈ t, IsCompact (P x)) ∧
      (∀ x ∈ t, connectedComponentIn S x ⊆ P x) ∧
      (∀ x ∈ t, Disjoint (P x) R) ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → Disjoint (P x) (P y)) ∧
      (⋃ x ∈ (t : Set X), P x) ∪ R = S := by
  classical
  obtain ⟨P, R, hR, hP, hp, hPR, hPP, hcover⟩ :=
    exists_compact_partition_finite_components hS t htS ht
  refine ⟨P, R, hR, hP, ?_, hPR, hPP, hcover⟩
  intro x hx y hy
  let B : Set X := (⋃ z ∈ ((t.erase x : Finset X) : Set X), P z) ∪ R
  have hB : IsCompact B := (t.erase x).isCompact_biUnion (by
    intro z hz
    exact hP z (Finset.mem_of_mem_erase hz)) |>.union hR
  have hdis : Disjoint (P x) B := by
    rw [disjoint_union_right, disjoint_iUnion_right]
    refine ⟨?_, hPR x hx⟩
    intro z
    rw [disjoint_iUnion_right]
    intro hz
    exact hPP x hx z (Finset.mem_of_mem_erase hz) (Finset.ne_of_mem_erase hz).symm
  have hU : P x ∪ B = S := by
    ext z
    rw [← hcover]
    simp only [B, mem_union, mem_iUnion, Finset.mem_coe, Finset.mem_erase]
    constructor
    · rintro (hz | ⟨w, ⟨hwx, hw⟩, hz⟩ | hz)
      · exact Or.inl ⟨x, hx, hz⟩
      · exact Or.inl ⟨w, hw, hz⟩
      · exact Or.inr hz
    · rintro (⟨w, hw, hz⟩ | hz)
      · by_cases hwx : w = x
        · subst w; exact Or.inl hz
        · exact Or.inr (Or.inl ⟨w, ⟨hwx, hw⟩, hz⟩)
      · exact Or.inr (Or.inr hz)
  by_contra hyP
  have hyS : y ∈ S := connectedComponentIn_subset S x hy
  have hyB : y ∈ B := (show y ∈ P x ∪ B from hU.symm ▸ hyS).resolve_left hyP
  exact ((not_mem_component_iff_compact_partition hS (htS x hx) hyS).mpr
    ⟨P x, B, hP x hx, hB, hdis, hU, hp x hx, hyB⟩) hy

end LatticeProb.Topology
