import LatticeProb.Topology.CompactOpenCofinal

/-! # Countable open enclosures with a fixed compact subset -/

set_option autoImplicit false

open Set TopologicalSpace

namespace LatticeProb.Topology

/-- A countable family of open sets containing a fixed compact set is cofinal
among open neighborhoods of that set and an additional compact set. -/
theorem exists_sequence_open_compact_enclosures_containing (X : Type*)
    [TopologicalSpace X] [SecondCountableTopology X] (A : Set X) (hA : IsCompact A) :
    ∃ V : ℕ → Set X, (∀ n, IsOpen (V n)) ∧ (∀ n, A ⊆ V n) ∧
      ∀ K : Set X, IsCompact K → ∀ U : Set X, IsOpen U → A ⊆ U → K ⊆ U →
        ∃ n, K ⊆ V n ∧ V n ⊆ U := by
  classical
  obtain ⟨W, hWo, hW⟩ := exists_sequence_open_compact_enclosures X
  let V : ℕ → Set X := fun n => if A ⊆ W n then W n else univ
  refine ⟨V, ?_, ?_, ?_⟩
  · intro n
    dsimp only [V]
    split_ifs <;> [exact hWo n; exact isOpen_univ]
  · intro n
    dsimp only [V]
    split_ifs with hn
    · exact hn
    · exact subset_univ A
  · intro K hK U hU hAU hKU
    obtain ⟨n, hn, hnU⟩ := hW (A ∪ K) (hA.union hK) U hU (union_subset hAU hKU)
    have hAW : A ⊆ W n := (subset_union_left : A ⊆ A ∪ K).trans hn
    refine ⟨n, ?_, ?_⟩
    · simpa only [V, ite_eq_left hAW] using (subset_union_right : K ⊆ A ∪ K).trans hn
    · simpa only [V, ite_eq_left hAW] using hnU

/-- Compact containment in random open sets is the union of containment
through the countable anchored family. -/
theorem compact_subset_open_iff_exists_anchored_enclosure {X Ω : Type*}
    [TopologicalSpace X] (A K : Set X) (V : ℕ → Set X)
    (hV : ∀ U : Set X, IsOpen U → A ⊆ U → K ⊆ U →
      ∃ n, K ⊆ V n ∧ V n ⊆ U)
    (U : Ω → Set X) (hU : ∀ ω, IsOpen (U ω)) (hAU : ∀ ω, A ⊆ U ω) :
    {ω | K ⊆ U ω} = ⋃ n, {ω | K ⊆ V n ∧ V n ⊆ U ω} := by
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · exact hV (U ω) (hU ω) (hAU ω)
  · rintro ⟨n, hnK, hnU⟩
    exact hnK.trans hnU

end LatticeProb.Topology
