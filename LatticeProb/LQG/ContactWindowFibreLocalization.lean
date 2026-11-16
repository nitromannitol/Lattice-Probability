import Mathlib.Data.Set.Image
import Mathlib.Topology.Connected.Basic

/-! # Fibre localization and components of image intersections -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A subset of an image intersection meets a third image precisely when one of
its cross-fibres has a representative in the third set. -/
theorem component_meets_image_iff_fibre_localization
    {α β : Type*} (f : α → β) (Q : α → α → Prop) (I J K : Set α) (C : Set β)
    (hQ : ∀ s t, f s = f t ↔ Q s t) (hC : C ⊆ Set.image f I ∩ Set.image f J) :
    (C ∩ Set.image f K).Nonempty ↔
      ∃ s ∈ I, ∃ t ∈ J, f s ∈ C ∧ Q s t ∧ ∃ k ∈ K, Q s k := by
  constructor
  · rintro ⟨z, hzC, k, hk, hkz⟩
    obtain ⟨⟨s, hs, hsz⟩, ⟨t, ht, htz⟩⟩ := hC hzC
    exact ⟨s, hs, t, ht, hsz ▸ hzC, (hQ s t).1 (hsz.trans htz.symm),
      k, hk, (hQ s k).1 (hsz.trans hkz.symm)⟩
  · rintro ⟨s, _, t, _, hsC, _, k, hk, hsk⟩
    have h := (hQ s k).2 hsk
    exact ⟨f s, hsC, k, hk, h.symm⟩

/-- A component meeting a set contained in a second component is equal to it. -/
theorem components_eq_of_meets_subset
    {β : Type*} [TopologicalSpace β] {S C D W : Set β}
    (hC : C ∈ Set.image (connectedComponentIn S) S) (hD : D ∈ Set.image (connectedComponentIn S) S)
    (hW : W ⊆ D) (hmeet : (C ∩ W).Nonempty) : C = D := by
  obtain ⟨z, hzC, hzW⟩ := hmeet
  obtain ⟨c, hc, rfl⟩ := hC
  obtain ⟨d, hd, rfl⟩ := hD
  exact (connectedComponentIn_eq hzC).trans (connectedComponentIn_eq (hW hzW)).symm

/-- A localized cross-fibre identifies its component with one of the two
components containing the respective selector images. -/
theorem component_eq_left_or_right_of_fibre_localization
    {α β : Type*} [TopologicalSpace β] (f : α → β) (Q : α → α → Prop)
    (I J Kₗ Kᵣ : Set α) (S C L R : Set β)
    (hQ : ∀ s t, f s = f t ↔ Q s t)
    (hC : C ∈ Set.image (connectedComponentIn S) S)
    (hL : L ∈ Set.image (connectedComponentIn S) S)
    (hR : R ∈ Set.image (connectedComponentIn S) S)
    (hleft : Set.image f Kₗ ⊆ L) (hright : Set.image f Kᵣ ⊆ R)
    (hloc : ∃ s ∈ I, ∃ t ∈ J, f s ∈ C ∧ Q s t ∧
      ∃ k ∈ Kₗ ∪ Kᵣ, Q s k) : C = L ∨ C = R := by
  obtain ⟨s, _, t, _, hsC, _, k, hk, hsk⟩ := hloc
  have heq := (hQ s k).2 hsk
  rcases hk with hk | hk
  · left
    apply components_eq_of_meets_subset hC hL hleft
    exact ⟨f s, hsC, k, hk, heq.symm⟩
  · right
    apply components_eq_of_meets_subset hC hR hright
    exact ⟨f s, hsC, k, hk, heq.symm⟩

end LatticeProb
