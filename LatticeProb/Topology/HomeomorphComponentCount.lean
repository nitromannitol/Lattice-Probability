import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Set.Card

/-! # Connected component counts under homeomorphisms -/

set_option autoImplicit false

open Set TopologicalSpace

namespace LatticeProb

/-- A homeomorphism preserves the number of non-singleton connected components
of a set, including the convention for infinitely many components. -/
theorem ncard_nonsubsingleton_components_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (S : Set X) :
    {C ∈ connectedComponentIn (h '' S) '' (h '' S) | ¬ C.Subsingleton}.ncard =
      {C ∈ connectedComponentIn S '' S | ¬ C.Subsingleton}.ncard := by
  classical
  have himage : (fun C : Set X => h '' C) ''
      {C ∈ connectedComponentIn S '' S | ¬ C.Subsingleton} =
      {C ∈ connectedComponentIn (h '' S) '' (h '' S) | ¬ C.Subsingleton} := by
    ext C
    constructor
    · rintro ⟨D, ⟨⟨x, hx, rfl⟩, hD⟩, rfl⟩
      exact ⟨⟨h x, ⟨x, hx, rfl⟩, (h.image_connectedComponentIn hx).symm⟩,
        fun hs => hD (h.injective.subsingleton_image_iff.mp hs)⟩
    · rintro ⟨⟨y, ⟨x, hx, rfl⟩, rfl⟩, hC⟩
      refine ⟨connectedComponentIn S x, ⟨⟨x, hx, rfl⟩, ?_⟩,
        h.image_connectedComponentIn hx⟩
      intro hs
      apply hC
      rw [← h.image_connectedComponentIn hx]
      exact h.injective.subsingleton_image_iff.mpr hs
  rw [← himage]
  exact Set.ncard_image_of_injective _ h.injective.image_injective

/-- A homeomorphism preserves the number of non-singleton components in
an intersection. -/
theorem ncard_nonsubsingleton_inter_components_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (A B : Set X) :
    {C ∈ connectedComponentIn (h '' A ∩ h '' B) '' (h '' A ∩ h '' B) |
        ¬ C.Subsingleton}.ncard =
      {C ∈ connectedComponentIn (A ∩ B) '' (A ∩ B) | ¬ C.Subsingleton}.ncard := by
  simpa only [Set.image_inter h.injective] using
    ncard_nonsubsingleton_components_image h (A ∩ B)

end LatticeProb
