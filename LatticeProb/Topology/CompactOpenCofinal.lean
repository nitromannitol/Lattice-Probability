import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Set.Countable

/-! # Countable open neighborhoods of compact sets -/

set_option autoImplicit false

open Set TopologicalSpace

namespace LatticeProb.Topology

/-- A fixed countable family of open sets is cofinal between compact sets and
    their open neighborhoods. -/
theorem exists_sequence_open_compact_enclosures (X : Type*) [TopologicalSpace X]
    [SecondCountableTopology X] :
    ∃ V : ℕ → Set X, (∀ n, IsOpen (V n)) ∧
      ∀ K : Set X, IsCompact K → ∀ U : Set X, IsOpen U → K ⊆ U →
        ∃ n, K ⊆ V n ∧ V n ⊆ U := by
  classical
  let B : Set (Set X) := countableBasis X
  let S : Set (Set X) := sUnion '' {t : Set (Set X) | t.Finite ∧ t ⊆ B}
  have hSc : S.Countable := (countable_ofPred_finite_subset (countable_countableBasis X)).image _
  have hSo : ∀ V ∈ S, IsOpen V := by
    rintro V ⟨t, ⟨_, ht⟩, rfl⟩
    exact isOpen_sUnion fun W hW => isOpen_of_mem_countableBasis (ht hW)
  have hSn : S.Nonempty := ⟨∅, ⟨∅, ⟨finite_empty, empty_subset B⟩, sUnion_empty⟩⟩
  obtain ⟨V, hV⟩ := hSc.exists_eq_range hSn
  refine ⟨V, fun n => hSo _ (hV.symm ▸ mem_range_self n), ?_⟩
  intro K hK U hU hKU
  let b : Set (Set X) := {W | W ∈ B ∧ W ⊆ U}
  have hcover : K ⊆ ⋃ W ∈ b, W := by
    intro x hx
    obtain ⟨W, hWB, hxW, hWU⟩ :=
      (isBasis_countableBasis X).exists_subset_of_mem_open (hKU hx) hU
    exact mem_iUnion_of_mem W (mem_iUnion_of_mem ⟨hWB, hWU⟩ hxW)
  obtain ⟨t, htb, htf, hKt⟩ := hK.elim_finite_subcover_image
    (fun W hW => isOpen_of_mem_countableBasis hW.1) hcover
  have htS : ⋃₀ t ∈ S := ⟨t, ⟨htf, fun W hW => (htb hW).1⟩, rfl⟩
  obtain ⟨n, hn⟩ := hV ▸ htS
  refine ⟨n, ?_, ?_⟩
  · rw [hn]
    intro x hx
    obtain ⟨W, hWt, hxW⟩ := mem_iUnion₂.mp (hKt hx)
    exact mem_sUnion.mpr ⟨W, hWt, hxW⟩
  · rw [hn]
    rintro x ⟨W, hWt, hxW⟩
    exact (htb hWt).2 hxW

end LatticeProb.Topology
