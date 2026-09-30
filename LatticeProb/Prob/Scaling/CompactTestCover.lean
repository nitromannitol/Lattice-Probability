/- Countably many compact sets suffice to enclose compact subsets of arbitrary open sets.

Moved from Parking-Sharpness.
-/
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Hausdorff

open Set TopologicalSpace Filter Topology
namespace LatticeProb.Scaling.CompactTestCover

/-- A countable family of compact sets such that every compact subset of an open set is
enclosed by, and encloses into, a member of the family. -/
theorem exists_countable_compact_enclosures (X : Type*) [TopologicalSpace X]
    [SecondCountableTopology X] [LocallyCompactSpace X] [T2Space X] :
    ∃ S : Set (Set X), S.Countable ∧ (∀ K ∈ S, IsCompact K) ∧
      ∀ K : Set X, IsCompact K → ∀ O : Set X, IsOpen O → K ⊆ O →
        ∃ L ∈ S, K ⊆ L ∧ L ⊆ O := by
  classical
  let B : Set (Set X) := {U | U ∈ countableBasis X ∧ IsCompact (closure U)}
  have hBc : B.Countable := (countable_countableBasis X).mono fun _ h => h.1
  let S : Set (Set X) := (fun t : Set (Set X) => ⋃₀ (closure '' t)) ''
    {t : Set (Set X) | t.Finite ∧ t ⊆ B}
  refine ⟨S, (countable_setOf_finite_subset hBc).image _, ?_, ?_⟩
  · rintro L ⟨t, ⟨ht, htB⟩, rfl⟩
    apply (ht.image closure).isCompact_sUnion
    rintro _ ⟨U, hU, rfl⟩
    exact (htB hU).2
  · intro K hK O hO hKO
    let b : Set (Set X) := {U | U ∈ B ∧ closure U ⊆ O}
    have hcover : K ⊆ ⋃ U ∈ b, U := by
      intro x hx
      obtain ⟨C, hCx, hCO, hCc⟩ :=
        LocallyCompactSpace.local_compact_nhds (x := x) O (hO.mem_nhds (hKO hx))
      obtain ⟨U, hUb, hxU, hUC⟩ := (isBasis_countableBasis X).mem_nhds_iff.mp hCx
      have hcl : closure U ⊆ C := closure_minimal hUC hCc.isClosed
      have hU : U ∈ b := ⟨⟨hUb, hCc.of_isClosed_subset isClosed_closure hcl⟩, hcl.trans hCO⟩
      exact mem_iUnion_of_mem U (mem_iUnion_of_mem hU hxU)
    obtain ⟨t, htb, htf, hKt⟩ := hK.elim_finite_subcover_image
      (fun U hU => isOpen_of_mem_countableBasis hU.1.1) hcover
    refine ⟨⋃₀ (closure '' t), ⟨t, ⟨htf, fun U hU => (htb hU).1⟩, rfl⟩, ?_, ?_⟩
    · intro x hx
      obtain ⟨U, hUt, hxU⟩ := mem_iUnion₂.mp (hKt hx)
      exact mem_sUnion.mpr ⟨closure U, mem_image_of_mem closure hUt, subset_closure hxU⟩
    · rintro x ⟨C, ⟨U, hUt, rfl⟩, hxC⟩
      exact (htb hUt).2 hxC

/-- A sequence version of the compact enclosure family. -/
theorem exists_sequence_compact_enclosures (X : Type*) [TopologicalSpace X]
    [SecondCountableTopology X] [LocallyCompactSpace X] [T2Space X] :
    ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧
      ∀ C : Set X, IsCompact C → ∀ O : Set X, IsOpen O → C ⊆ O →
        ∃ n, C ⊆ K n ∧ K n ⊆ O := by
  obtain ⟨S, hSc, hSK, hcover⟩ := exists_countable_compact_enclosures X
  have hS : S.Nonempty := by
    obtain ⟨L, hLS, _⟩ := hcover ∅ isCompact_empty univ isOpen_univ (empty_subset _)
    exact ⟨L, hLS⟩
  obtain ⟨K, hK⟩ := hSc.exists_eq_range hS
  refine ⟨K, fun n => hSK _ (hK.symm ▸ mem_range_self n), ?_⟩
  intro C hC O hO hCO
  obtain ⟨L, hLS, hCL, hLO⟩ := hcover C hC O hO hCO
  obtain ⟨n, rfl⟩ := hK ▸ hLS
  exact ⟨n, hCL, hLO⟩

end LatticeProb.Scaling.CompactTestCover
