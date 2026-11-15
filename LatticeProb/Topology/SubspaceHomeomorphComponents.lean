import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Connected.Basic

/-! # Connected components under subspace homeomorphisms -/

set_option autoImplicit false

open Set Topology

namespace LatticeProb

/-- A homeomorphism between subspaces maps a connected component into the
corresponding component whenever it maps the underlying set into that set. -/
theorem homeomorph_subspace_mem_connectedComponentIn
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {A : Set E} {B : Set F} (e : A ≃ₜ B) {s : Set E} {t : Set F}
    (hs : s ⊆ A)
    (ht : ∀ x : s, (e ⟨x.1, hs x.2⟩).1 ∈ t)
    (x z : s) (hz : z.1 ∈ connectedComponentIn s x.1) :
    (e ⟨z.1, hs z.2⟩).1 ∈ connectedComponentIn t (e ⟨x.1, hs x.2⟩).1 := by
  let C := connectedComponentIn s x.1
  have hCA : C ⊆ A := (connectedComponentIn_subset s x.1).trans hs
  have hpre : IsPreconnected ((Subtype.val : A → E) ⁻¹' C) := by
    apply IsInducing.subtypeVal.isPreconnected_image.mp
    simpa only [Subtype.image_preimage_coe, inter_eq_right.mpr hCA] using
      (isPreconnected_connectedComponentIn : IsPreconnected C)
  let g : A → F := fun y => (e y).1
  have hg : Continuous g := continuous_subtype_val.comp e.continuous
  have himage : IsPreconnected (g '' ((Subtype.val : A → E) ⁻¹' C)) :=
    hpre.image g hg.continuousOn
  have hpoint : g ⟨x.1, hs x.2⟩ ∈ g '' ((Subtype.val : A → E) ⁻¹' C) :=
    ⟨⟨x.1, hs x.2⟩, mem_connectedComponentIn x.2, rfl⟩
  have hsub : g '' ((Subtype.val : A → E) ⁻¹' C) ⊆ t := by
    rintro _ ⟨y, hy, rfl⟩
    exact ht ⟨y.1, connectedComponentIn_subset s x.1 hy⟩
  exact himage.subset_connectedComponentIn hpoint hsub ⟨⟨z.1, hs z.2⟩, hz, rfl⟩


/-- A homeomorphism between subspaces preserves component membership if it
maps the two underlying sets onto one another. -/
theorem homeomorph_subspace_mem_connectedComponentIn_iff
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {A : Set E} {B : Set F} (e : A ≃ₜ B) {s : Set E} {t : Set F}
    (hs : s ⊆ A) (ht : t ⊆ B)
    (hmem : ∀ y : A, y.1 ∈ s ↔ (e y).1 ∈ t)
    (x z : s) :
    (e ⟨z.1, hs z.2⟩).1 ∈ connectedComponentIn t (e ⟨x.1, hs x.2⟩).1 ↔
      z.1 ∈ connectedComponentIn s x.1 := by
  have hx : (e ⟨x.1, hs x.2⟩).1 ∈ t := (hmem ⟨x.1, hs x.2⟩).mp x.2
  have hz : (e ⟨z.1, hs z.2⟩).1 ∈ t := (hmem ⟨z.1, hs z.2⟩).mp z.2
  constructor
  · intro h
    have hback : ∀ y : t, (e.symm ⟨y.1, ht y.2⟩).1 ∈ s := by
      intro y
      apply (hmem (e.symm ⟨y.1, ht y.2⟩)).mpr
      simpa only [Homeomorph.apply_symm_apply] using y.2
    have H := homeomorph_subspace_mem_connectedComponentIn e.symm ht hback
      ⟨_, hx⟩ ⟨_, hz⟩ h
    change (e.symm (e ⟨z.1, hs z.2⟩)).1 ∈
      connectedComponentIn s (e.symm (e ⟨x.1, hs x.2⟩)).1 at H
    simpa only [Homeomorph.symm_apply_apply] using H
  · intro h
    exact homeomorph_subspace_mem_connectedComponentIn e hs
      (fun y => (hmem ⟨y.1, hs y.2⟩).mp y.2) x z h

end LatticeProb
