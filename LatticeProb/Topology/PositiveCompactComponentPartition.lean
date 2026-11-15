import LatticeProb.Topology.FiniteComponentCardinality

/-! # Positive finite component thresholds -/

set_option autoImplicit false

open Set TopologicalSpace

namespace LatticeProb.Topology

/-- A positive finite component threshold has disjoint compact partition
pieces containing connected non-singleton compact witnesses. -/
theorem succ_le_encard_nonSingletonComponents_iff_compact_partition
    {X : Type*} [TopologicalSpace X] [T2Space X] {S : Set X}
    (hS : IsCompact S) (n : ℕ) :
    (n + 1 : ℕ∞) ≤ (nonSingletonComponents S).encard ↔
    ∃ (P W : Fin (n + 1) → Set X),
      (∀ i, IsCompact (P i)) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (⋃ i, P i) = S ∧
      ∀ i, IsCompact (W i) ∧ IsConnected (W i) ∧ W i ⊆ P i ∧
        ¬ (W i).Subsingleton := by
  classical
  rw [show (n + 1 : ℕ∞) = ((n + 1 : ℕ) : ℕ∞) by simp only [Nat.cast_add, Nat.cast_one],
    le_encard_nonSingletonComponents_iff_compact_partition hS (n + 1)]
  constructor
  · rintro ⟨P, W, R, hR, hP, hPR, hPP, hcover, hW⟩
    let Q : Fin (n + 1) → Set X := fun i => if i = 0 then P i ∪ R else P i
    have hPQ (i : Fin (n + 1)) : P i ⊆ Q i := by
      by_cases hi : i = 0
      · simp only [Q, ite_eq_left hi]; exact subset_union_left
      · simp only [Q, ite_eq_right hi]; exact Subset.rfl
    refine ⟨Q, W, ?_, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = 0
      · simp only [Q, ite_eq_left hi]; exact (hP i).union hR
      · simp only [Q, ite_eq_right hi]; exact hP i
    · intro i j hij
      by_cases hi : i = 0
      · have hj : j ≠ 0 := by intro h; exact hij (hi.trans h.symm)
        simp only [Q, ite_eq_left hi, ite_eq_right hj, disjoint_union_left]
        exact ⟨hPP i j hij, (hPR j).symm⟩
      · by_cases hj : j = 0
        · simp only [Q, ite_eq_right hi, ite_eq_left hj, disjoint_union_right]
          exact ⟨hPP i j hij, hPR i⟩
        · simp only [Q, ite_eq_right hi, ite_eq_right hj]
          exact hPP i j hij
    · apply subset_antisymm
      · intro x hx
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        by_cases h : i = 0
        · have hx' : x ∈ P i ∪ R := by simpa only [Q, ite_eq_left h] using hi
          rw [← hcover]
          exact hx'.elim (fun hxP => Or.inl (mem_iUnion.mpr ⟨i, hxP⟩)) Or.inr
        · have hx' : x ∈ P i := by simpa only [Q, ite_eq_right h] using hi
          rw [← hcover]
          exact Or.inl (mem_iUnion.mpr ⟨i, hx'⟩)
      · intro x hx
        rw [← hcover] at hx
        rcases hx with hx | hx
        · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
          exact mem_iUnion.mpr ⟨i, hPQ i hi⟩
        · exact mem_iUnion.mpr ⟨0, by simp only [Q, ite_true, mem_union]; exact Or.inr hx⟩
    · intro i
      exact ⟨(hW i).1, (hW i).2.1, (hW i).2.2.1.trans (hPQ i), (hW i).2.2.2⟩
  · rintro ⟨P, W, hP, hPP, hcover, hW⟩
    exact ⟨P, W, ∅, isCompact_empty, hP, (fun i => disjoint_empty (P i)), hPP,
      by simpa only [union_empty] using hcover, hW⟩

end LatticeProb.Topology
