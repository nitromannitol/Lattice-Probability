import LatticeProb.Topology.NonCutPoints

/-!
# Sides of the cut points of a continuum with exactly two non-cut points

Let `X` be a compact connected `T₁` space and let `a ≠ b` be points of `X` such that `a` and `b` are the only
non-cut points of `X`: `X \ {x}` is connected exactly when `x = a` or `x = b`. This is the setting of the classical
characterisation of the arc (R. L. Moore; see Willard, *General Topology*, §28). For every `x : X` put

* `connectedComponentIn {x}ᶜ a`, the *side of `x` towards `a`*, and
* `connectedComponentIn {x}ᶜ b`, the *side of `x` towards `b`*.

This file proves (`isOpen_connectedComponentIn_compl_singleton_and`) that for every `x` these two sides are disjoint
open sets covering `X \ {x}`. For `x = a` the side towards `a` is empty and the side towards `b` is `X \ {a}`
(symmetrically for `x = b`). For a cut point `x`, every separation `X \ {x} = A ∪ B` puts `a` and `b` on different
sides (each side contains a non-cut point, `exists_isPreconnected_compl_singleton_mem_of_union_eq_compl_singleton`),
and the side containing `a` is connected, because a further splitting of it would give a separation of `X \ {x}` with
a side containing neither `a` nor `b`. Hence the two sides of the separation are the components of `a` and of `b`.

These sides are the open rays of the separation order of `X`, which identifies `X` with an arc.
-/

namespace LatticeProb.Topology

open Set

variable {X : Type*} [TopologicalSpace X] [T1Space X] [CompactSpace X] [ConnectedSpace X] {a b : X}

/-- If `a` and `b` are the only non-cut points, then every nonempty side `A` of a separation of `X \ {x}` contains
`a` or `b`. -/
theorem mem_or_mem_of_union_eq_compl_singleton_of_isPreconnected_iff
    (honly : ∀ x : X, IsPreconnected ({x}ᶜ : Set X) ↔ x = a ∨ x = b) {x : X} {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B) (hcover : A ∪ B = {x}ᶜ) (hAne : A.Nonempty) :
    a ∈ A ∨ b ∈ A := by
  obtain ⟨y, hyA, hy⟩ :=
    exists_isPreconnected_compl_singleton_mem_of_union_eq_compl_singleton hA hB hAB hcover hAne
  rcases (honly y).1 hy with h | h
  · exact Or.inl (h ▸ hyA)
  · exact Or.inr (h ▸ hyA)

/-- If `a` and `b` are the only non-cut points and a separation `X \ {x} = A ∪ B` has `a ∈ A`, then `b ∈ B`. -/
theorem mem_right_of_union_eq_compl_singleton_of_isPreconnected_iff
    (honly : ∀ x : X, IsPreconnected ({x}ᶜ : Set X) ↔ x = a ∨ x = b) {x : X} {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B) (hcover : A ∪ B = {x}ᶜ) (haA : a ∈ A)
    (hBne : B.Nonempty) : b ∈ B := by
  rcases mem_or_mem_of_union_eq_compl_singleton_of_isPreconnected_iff honly hB hA hAB.symm
      ((union_comm B A).trans hcover) hBne with h | h
  · exact absurd h (disjoint_left.1 hAB haA)
  · exact h

/-- If `a` and `b` are the only non-cut points, then the side containing `a` of a separation `X \ {x} = A ∪ B` is
the connected component of `a` in `X \ {x}`. -/
theorem connectedComponentIn_compl_singleton_eq_of_isPreconnected_iff
    (honly : ∀ x : X, IsPreconnected ({x}ᶜ : Set X) ↔ x = a ∨ x = b) {x : X} {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B) (hcover : A ∪ B = {x}ᶜ) (haA : a ∈ A)
    (hBne : B.Nonempty) : connectedComponentIn {x}ᶜ a = A := by
  have hbB := mem_right_of_union_eq_compl_singleton_of_isPreconnected_iff honly hA hB hAB hcover haA hBne
  -- a splitting `A = (A ∩ u) ∪ (A ∩ v)` with `a ∈ u` gives the separation `(A ∩ v) ∪ ((A ∩ u) ∪ B)` of `X \ {x}`,
  -- whose first side contains neither `a` nor `b`
  have key : ∀ u v : Set X, IsOpen u → IsOpen v → A ⊆ u ∪ v → A ∩ (u ∩ v) = ∅ → a ∈ u →
      (A ∩ v).Nonempty → False := by
    intro u v hu hv hAuv huv hau hAv
    have hdisj : Disjoint (A ∩ v) ((A ∩ u) ∪ B) := by
      refine disjoint_left.2 fun y hy hy' => ?_
      rcases hy' with hy' | hy'
      · have hy'' : y ∈ A ∩ (u ∩ v) := ⟨hy.1, hy'.2, hy.2⟩
        rw [huv] at hy''
        exact hy''
      · exact disjoint_left.1 hAB hy.1 hy'
    have hcov : (A ∩ v) ∪ ((A ∩ u) ∪ B) = {x}ᶜ := by
      rw [← hcover]
      apply subset_antisymm
      · rintro y (⟨hy, -⟩ | ⟨hy, -⟩ | hy)
        · exact Or.inl hy
        · exact Or.inl hy
        · exact Or.inr hy
      · rintro y (hy | hy)
        · rcases hAuv hy with hu' | hv'
          · exact Or.inr (Or.inl ⟨hy, hu'⟩)
          · exact Or.inl ⟨hy, hv'⟩
        · exact Or.inr (Or.inr hy)
    rcases mem_or_mem_of_union_eq_compl_singleton_of_isPreconnected_iff honly (hA.inter hv)
        ((hA.inter hu).union hB) hdisj hcov hAv with h | h
    · have h' : a ∈ A ∩ (u ∩ v) := ⟨haA, hau, h.2⟩
      rw [huv] at h'
      exact h'
    · exact disjoint_left.1 hAB h.1 hbB
  have hApre : IsPreconnected A := by
    intro u v hu hv hAuv hAu hAv
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rcases hAuv haA with hau | hav
    · exact key u v hu hv hAuv hne hau hAv
    · exact key v u hv hu (by rwa [union_comm]) (by rwa [inter_comm v u]) hav hAu
  apply subset_antisymm
  · have hsub : connectedComponentIn {x}ᶜ a ⊆ A ∪ B := hcover ▸ connectedComponentIn_subset _ _
    rcases isPreconnected_connectedComponentIn.subset_or_subset hA hB hAB hsub with h | h
    · exact h
    · have hax : a ∈ ({x}ᶜ : Set X) := hcover ▸ Or.inl haA
      exact absurd (h (mem_connectedComponentIn hax)) (disjoint_left.1 hAB haA)
  · exact hApre.subset_connectedComponentIn haA (hcover ▸ subset_union_left)

/-- **The two sides of a point.** In a compact connected `T₁` space whose only non-cut points are `a ≠ b`, for every
`x` the components of `a` and of `b` in `X \ {x}` are disjoint open sets covering `X \ {x}`. -/
theorem isOpen_connectedComponentIn_compl_singleton_and (hab : a ≠ b)
    (honly : ∀ x : X, IsPreconnected ({x}ᶜ : Set X) ↔ x = a ∨ x = b) (x : X) :
    IsOpen (connectedComponentIn {x}ᶜ a) ∧ IsOpen (connectedComponentIn {x}ᶜ b) ∧
      Disjoint (connectedComponentIn {x}ᶜ a) (connectedComponentIn {x}ᶜ b) ∧
      connectedComponentIn {x}ᶜ a ∪ connectedComponentIn {x}ᶜ b = {x}ᶜ := by
  have honly' : ∀ x : X, IsPreconnected ({x}ᶜ : Set X) ↔ x = b ∨ x = a := fun x => (honly x).trans or_comm
  by_cases hx : IsPreconnected ({x}ᶜ : Set X)
  · rcases (honly x).1 hx with h | h
    · rw [h] at hx ⊢
      rw [connectedComponentIn_eq_empty (F := {a}ᶜ) (x := a) (by simp),
        hx.connectedComponentIn (mem_compl_singleton_iff.2 hab.symm)]
      exact ⟨isOpen_empty, isOpen_compl_singleton, empty_disjoint _, empty_union _⟩
    · rw [h] at hx ⊢
      rw [connectedComponentIn_eq_empty (F := {b}ᶜ) (x := b) (by simp),
        hx.connectedComponentIn (mem_compl_singleton_iff.2 hab)]
      exact ⟨isOpen_compl_singleton, isOpen_empty, disjoint_empty _, union_empty _⟩
  · obtain ⟨A, B, hA, hB, hAB, hcover, hAne, hBne⟩ :=
      exists_separation_of_not_isPreconnected_compl_singleton hx
    have hcover' : B ∪ A = {x}ᶜ := (union_comm B A).trans hcover
    rcases mem_or_mem_of_union_eq_compl_singleton_of_isPreconnected_iff honly hA hB hAB hcover hAne
      with haA | hbA
    · have hbB := mem_right_of_union_eq_compl_singleton_of_isPreconnected_iff honly hA hB hAB hcover haA hBne
      rw [connectedComponentIn_compl_singleton_eq_of_isPreconnected_iff honly hA hB hAB hcover haA hBne,
        connectedComponentIn_compl_singleton_eq_of_isPreconnected_iff honly' hB hA hAB.symm hcover' hbB hAne]
      exact ⟨hA, hB, hAB, hcover⟩
    · have haB := mem_right_of_union_eq_compl_singleton_of_isPreconnected_iff honly' hA hB hAB hcover hbA hBne
      rw [connectedComponentIn_compl_singleton_eq_of_isPreconnected_iff honly hB hA hAB.symm hcover' haB hAne,
        connectedComponentIn_compl_singleton_eq_of_isPreconnected_iff honly' hA hB hAB hcover hbA hBne]
      exact ⟨hB, hA, hAB.symm, hcover'⟩

end LatticeProb.Topology
