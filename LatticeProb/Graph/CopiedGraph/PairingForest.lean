/-
# Pairings as rooted copied forests

An acyclic copied edge set covering every vertex by the paired terminal lists
is a forest rooted at the first list. Conversely, root uniqueness and the
prescribed matching walks give exact pairing connectivity and separation.
The proof follows copied walks, so all original edge identities are retained.
-/
import LatticeProb.Graph.CopiedGraph.RootedForest



namespace LatticeProb.Graph.CopiedGraph

variable {V E ι : Type*}

private theorem roots_eq_of_reaches (J : CopiedGraph V E) {F : Finset E} {R : Set V}
    (h : J.IsRootedForest R F) {x r s : V} (hr : r ∈ R) (hs : s ∈ R)
    (hxr : J.reaches F x r) (hxs : J.reaches F x s) : r = s := by
  obtain ⟨q, _, _, hq⟩ := h.2 x
  exact (hq r hr hxr).trans (hq s hs hxs).symm

/-- **Pairing and rooted-forest equivalence.** Rooting at the injective list
`a` and requiring `a r` to reach `b (π r)` is equivalent to the literal
pairing-grove predicate: acyclicity, complete terminal coverage, exact
permuted cross connectivity, and separation of distinct first-list roots.
No connectedness, cardinality, looplessness, or planarity premise is needed. -/
theorem isRootedForest_range_and_matching_iff (J : CopiedGraph V E)
    (a b : ι → V) (ha : Function.Injective a) (π : Equiv.Perm ι) (F : Finset E) :
    (J.IsRootedForest (Set.range a) F ∧ ∀ r, J.reaches F (a r) (b (π r))) ↔
      J.IsForest F ∧
      (∀ x, ∃ r, J.reaches F x (a r) ∨ J.reaches F x (b r)) ∧
      (∀ r s, J.reaches F (a r) (b s) ↔ s = π r) ∧
      (∀ r s, r ≠ s → ¬J.reaches F (a r) (a s)) := by
  constructor
  · rintro ⟨hR, hmatch⟩
    refine ⟨hR.1, ?_, ?_, ?_⟩
    · intro x
      obtain ⟨r, ⟨i, rfl⟩, hxi, _⟩ := hR.2 x
      exact ⟨i, Or.inl hxi⟩
    · intro r s
      constructor
      · intro hrs
        have hs : J.reaches F (a (π.symm s)) (b s) := by
          simpa only [Equiv.apply_symm_apply] using hmatch (π.symm s)
        have he : a r = a (π.symm s) := roots_eq_of_reaches J hR
          ⟨r, rfl⟩ ⟨π.symm s, rfl⟩ .refl (hrs.trans (J.reaches_symm hs))
        have hi : r = π.symm s := ha he
        rw [hi, Equiv.apply_symm_apply]
      · rintro rfl
        exact hmatch r
    · intro r s hne hrs
      exact hne (ha (roots_eq_of_reaches J hR ⟨r, rfl⟩ ⟨s, rfl⟩ .refl hrs))
  · rintro ⟨hforest, hcover, hcross, hsep⟩
    have hmatch (r : ι) : J.reaches F (a r) (b (π r)) := (hcross r (π r)).mpr rfl
    have hcoverA (x : V) : ∃ r, J.reaches F x (a r) := by
      obtain ⟨r, hxr | hxr⟩ := hcover x
      · exact ⟨r, hxr⟩
      · have hs : J.reaches F (a (π.symm r)) (b r) := by
          simpa only [Equiv.apply_symm_apply] using hmatch (π.symm r)
        exact ⟨π.symm r, hxr.trans (J.reaches_symm hs)⟩
    refine ⟨⟨hforest, ?_⟩, hmatch⟩
    intro x
    obtain ⟨r, hxr⟩ := hcoverA x
    refine ⟨a r, ⟨r, rfl⟩, hxr, ?_⟩
    rintro _ ⟨s, rfl⟩ hxs
    have he : s = r := by
      by_contra hne
      exact hsep s r hne ((J.reaches_symm hxs).trans hxr)
    exact congrArg a he

end LatticeProb.Graph.CopiedGraph
