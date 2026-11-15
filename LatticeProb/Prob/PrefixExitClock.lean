import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # First exit of a path prefix -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- The infimum of times whose prefix leaves a set is the pointwise exit
infimum. Both sides use the real infimum convention when there is no exit. -/
theorem sInf_prefix_exit_eq_sInf_pointwise_exit {E : Type*}
    (f : ℝ → E) (U : Set E) (a : ℝ) :
    sInf {t : ℝ | a ≤ t ∧ ¬ f '' Icc a t ⊆ U} =
      sInf {t : ℝ | a ≤ t ∧ f t ∉ U} := by
  classical
  by_cases h : ∃ t : ℝ, a ≤ t ∧ f t ∉ U
  · have hpoint : {t : ℝ | a ≤ t ∧ f t ∉ U}.Nonempty := h
    have hprefix : {t : ℝ | a ≤ t ∧ ¬ f '' Icc a t ⊆ U}.Nonempty := by
      obtain ⟨t, ht, htu⟩ := h
      exact ⟨t, ht, fun hs => htu (hs ⟨t, ⟨ht, le_rfl⟩, rfl⟩)⟩
    have hpoint_bdd : BddBelow {t : ℝ | a ≤ t ∧ f t ∉ U} :=
      ⟨a, fun _ ht => ht.1⟩
    have hprefix_bdd : BddBelow {t : ℝ | a ≤ t ∧ ¬ f '' Icc a t ⊆ U} :=
      ⟨a, fun _ ht => ht.1⟩
    apply le_antisymm
    · apply le_csInf hpoint
      intro t ht
      exact csInf_le hprefix_bdd ⟨ht.1, fun hs => ht.2 (hs ⟨t, ⟨ht.1, le_rfl⟩, rfl⟩)⟩
    · apply le_csInf hprefix
      intro t ht
      have hex : ∃ s ∈ Icc a t, f s ∉ U := by
        by_contra hn
        apply ht.2
        intro y hy
        obtain ⟨s, hs, rfl⟩ := hy
        by_contra hsu
        exact hn ⟨s, hs, hsu⟩
      obtain ⟨s, hs, hsu⟩ := hex
      exact (csInf_le hpoint_bdd ⟨hs.1, hsu⟩).trans hs.2
  · have hp : {t : ℝ | a ≤ t ∧ f t ∉ U} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro t ht
      exact h ⟨t, ht⟩
    have hq : {t : ℝ | a ≤ t ∧ ¬ f '' Icc a t ⊆ U} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro t ht
      apply ht.2
      intro y hy
      obtain ⟨s, hs, rfl⟩ := hy
      by_contra hsu
      exact h ⟨s, hs.1, hsu⟩
    rw [hp, hq]

end LatticeProb
