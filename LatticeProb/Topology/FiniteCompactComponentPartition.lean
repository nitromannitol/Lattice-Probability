import LatticeProb.Topology.FiniteCompactComponentSeparation

/-! # Finite partitions separating components of a compact set -/

set_option autoImplicit false

open Set TopologicalSpace

namespace LatticeProb.Topology

/-- Finitely many points in distinct components of a compact Hausdorff set
belong to pairwise disjoint compact pieces, with a compact residual piece. -/
theorem exists_compact_partition_finite_components
    {X : Type*} [TopologicalSpace X] [T2Space X] {S : Set X}
    (hS : IsCompact S) (t : Finset X) (htS : ∀ x ∈ t, x ∈ S)
    (ht : ∀ x ∈ t, ∀ y ∈ t, x ≠ y →
      connectedComponentIn S x ≠ connectedComponentIn S y) :
    ∃ (P : X → Set X) (R : Set X),
      IsCompact R ∧ (∀ x ∈ t, IsCompact (P x)) ∧
      (∀ x ∈ t, x ∈ P x) ∧
      (∀ x ∈ t, Disjoint (P x) R) ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → Disjoint (P x) (P y)) ∧
      (⋃ x ∈ (t : Set X), P x) ∪ R = S := by
  classical
  induction t using Finset.induction_on generalizing S with
  | empty =>
    refine ⟨fun _ => ∅, S, hS, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp
  | @insert x t hxt ih =>
    have hxS : x ∈ S := htS x (Finset.mem_insert_self x t)
    have htS' : ∀ y ∈ t, y ∈ S := fun y hy => htS y (Finset.mem_insert_of_mem hy)
    have hsep : ∀ y ∈ t, y ∉ connectedComponentIn S x := by
      intro y hy hmem
      have hxy : x ≠ y := by
        intro h
        subst y
        exact hxt hy
      exact ht x (Finset.mem_insert_self x t) y (Finset.mem_insert_of_mem hy) hxy
        (connectedComponentIn_eq hmem)
    obtain ⟨A, B, hA, hB, hAB, hU, hxA, htB⟩ :=
      exists_compact_partition_separating_finite hS hxS t htS' hsep
    have hBS : B ⊆ S := by
      intro z hz
      rw [← hU]
      exact Or.inr hz
    have htBcomp : ∀ y ∈ t, ∀ z ∈ t, y ≠ z →
        connectedComponentIn B y ≠ connectedComponentIn B z := by
      intro y hy z hz hyz heq
      have hzBy : z ∈ connectedComponentIn B y := by
        rw [heq]
        exact mem_connectedComponentIn (htB z hz)
      have hzSy : z ∈ connectedComponentIn S y := connectedComponentIn_mono y hBS hzBy
      exact ht y (Finset.mem_insert_of_mem hy) z (Finset.mem_insert_of_mem hz) hyz
        (connectedComponentIn_eq hzSy)
    obtain ⟨P, R, hR, hP, hp, hPR, hPP, hcover⟩ := ih hB htB htBcomp
    have hPsub : ∀ y ∈ t, P y ⊆ B := by
      intro y hy z hz
      rw [← hcover]
      exact Or.inl (mem_iUnion.2 ⟨y, mem_iUnion.2 ⟨hy, hz⟩⟩)
    have hRsub : R ⊆ B := by
      intro z hz
      rw [← hcover]
      exact Or.inr hz
    refine ⟨fun y => if y = x then A else P y, R, hR, ?_, ?_, ?_, ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · simpa using hA
      · have hyx : y ≠ x := fun h => hxt (h ▸ hy)
        simpa [hyx] using hP y hy
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · simpa using hxA
      · have hyx : y ≠ x := fun h => hxt (h ▸ hy)
        simpa [hyx] using hp y hy
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · simpa using hAB.mono_right hRsub
      · have hyx : y ≠ x := fun h => hxt (h ▸ hy)
        simpa [hyx] using hPR y hy
    · intro y hy z hz hyz
      rcases Finset.mem_insert.mp hy with hyx | hy
      · subst y
        have hzx : z ≠ x := fun h => hyz h.symm
        have hz' : z ∈ t := (Finset.mem_insert.mp hz).resolve_left hzx
        simpa [hzx] using hAB.mono_right (hPsub z hz')
      · have hyx : y ≠ x := fun h => hxt (h ▸ hy)
        rcases Finset.mem_insert.mp hz with hzx | hz
        · subst z
          simpa [hyx] using (hAB.mono_right (hPsub y hy)).symm
        · have hzx : z ≠ x := fun h => hxt (h ▸ hz)
          simpa [hyx, hzx] using hPP y hy z hz hyz
    · ext z
      simp only [mem_union, mem_iUnion, Finset.mem_coe, Finset.mem_insert]
      rw [← hU, ← hcover]
      simp only [mem_union, mem_iUnion, Finset.mem_coe]
      constructor
      · rintro (⟨y, hy, hz⟩ | hz)
        · rcases hy with rfl | hy
          · exact Or.inl (by simpa using hz)
          · by_cases hyx : y = x
            · subst y; exact False.elim (hxt hy)
            · exact Or.inr (Or.inl ⟨y, hy, by simpa [hyx] using hz⟩)
        · exact Or.inr (Or.inr hz)
      · rintro (hz | ⟨y, hy, hz⟩ | hz)
        · exact Or.inl ⟨x, Or.inl rfl, by simpa using hz⟩
        · have hyx : y ≠ x := fun h => hxt (h ▸ hy)
          exact Or.inl ⟨y, Or.inr hy, by simpa [hyx] using hz⟩
        · exact Or.inr hz

end LatticeProb.Topology
