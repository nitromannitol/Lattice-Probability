import LatticeProb.Topology.FiniteCompactComponentWitnesses
import LatticeProb.Topology.RandomShiftedCellComponentArray
import Mathlib.SetTheory.Cardinal.Embedding

/-! # Finite thresholds for non-singleton components -/

set_option autoImplicit false

open Set TopologicalSpace

namespace LatticeProb.Topology

/-- A finite lower bound for the extended cardinality is witnessed by points
in distinct non-singleton components. -/
theorem le_encard_nonSingletonComponents_iff
    {X : Type*} [TopologicalSpace X] (S : Set X) (n : ℕ) :
    (n : ℕ∞) ≤ (nonSingletonComponents S).encard ↔
      ∃ x : Fin n → X, (∀ i, x i ∈ S) ∧
        Function.Injective (fun i => connectedComponentIn S (x i)) ∧
        ∀ i, ¬ (connectedComponentIn S (x i)).Subsingleton := by
  classical
  constructor
  · intro h
    obtain ⟨f, _⟩ := Fin.Embedding.exists_embedding_disjoint_range_of_add_le_ENat_card
      (n := n) (s := (∅ : Set (nonSingletonComponents S)))
      (by simpa only [Set.ncard_empty, Nat.zero_add, Nat.cast_zero, zero_add,
        ENat.card_coe_set_eq] using h)
    have hf : ∀ i, ∃ x ∈ S, connectedComponentIn S x = (f i : Set X) := by
      intro i
      exact (f i).property.1
    choose x hxS hxc using hf
    refine ⟨x, hxS, ?_, ?_⟩
    · intro i j hij
      apply f.injective
      apply Subtype.ext
      exact (hxc i).symm.trans (hij.trans (hxc j))
    · intro i
      rw [hxc i]
      exact (f i).property.2
  · rintro ⟨x, hxS, hinj, hn⟩
    let f : Fin n ↪ nonSingletonComponents S :=
      ⟨fun i => ⟨connectedComponentIn S (x i), ⟨⟨x i, hxS i, rfl⟩, hn i⟩⟩,
        fun i j h => hinj (congrArg Subtype.val h)⟩
    have h := ENat.card_le_card_of_injective f.injective
    simpa only [ENat.card_eq_coe_fintype_card, Fintype.card_fin,
      ENat.card_coe_set_eq] using h

/-- Finite cardinality thresholds of compact sets admit compact partition
witnesses, including when the total number of components is infinite. -/
theorem le_encard_nonSingletonComponents_iff_compact_partition
    {X : Type*} [TopologicalSpace X] [T2Space X] {S : Set X}
    (hS : IsCompact S) (n : ℕ) :
    (n : ℕ∞) ≤ (nonSingletonComponents S).encard ↔
    ∃ (P W : Fin n → Set X) (R : Set X),
      IsCompact R ∧ (∀ i, IsCompact (P i)) ∧
      (∀ i, Disjoint (P i) R) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (⋃ i, P i) ∪ R = S ∧
      ∀ i, IsCompact (W i) ∧ IsConnected (W i) ∧ W i ⊆ P i ∧
        ¬ (W i).Subsingleton :=
  (le_encard_nonSingletonComponents_iff S n).trans
    (finite_nonsubsingleton_components_iff_compact_partition hS n)

end LatticeProb.Topology
