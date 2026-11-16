import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-! # Restriction of a family of sigma algebras to a measurable carrier -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- Restricting an intersection of sigma algebras to a set measurable in each
member agrees with intersecting their restrictions. -/
theorem comap_subtype_iInf_of_measurable {Ω ι : Type*}
    (F : ι → MeasurableSpace Ω) (A : Set Ω)
    (hA : ∀ i, MeasurableSet[F i] A) :
    MeasurableSpace.comap (Subtype.val : A → Ω) (⨅ i, F i) =
      ⨅ i, MeasurableSpace.comap (Subtype.val : A → Ω) (F i) := by
  apply le_antisymm
  · exact le_iInf fun i => MeasurableSpace.comap_mono (iInf_le F i)
  · intro s hs
    have hs' := MeasurableSpace.measurableSet_iInf.mp hs
    refine ⟨Subtype.val '' s, MeasurableSpace.measurableSet_iInf.mpr ?_, ?_⟩
    · intro i
      obtain ⟨t, ht, heq⟩ := hs' i
      have himage : Subtype.val '' s = A ∩ t := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨y.property, by
            change y ∈ (Subtype.val : A → Ω) ⁻¹' t
            rw [heq]
            exact hy⟩
        · rintro ⟨hxA, hxt⟩
          refine ⟨⟨x, hxA⟩, ?_, rfl⟩
          rw [← heq]
          exact hxt
      rw [himage]
      exact (hA i).inter ht
    · exact Set.preimage_image_eq s Subtype.val_injective

/-- A joined observation history may be restricted after taking the germ. -/
theorem comap_subtype_sup_iInf_of_measurable {Ω ι : Type*}
    (H : MeasurableSpace Ω) (F : ι → MeasurableSpace Ω) (A : Set Ω)
    (hA : ∀ i, MeasurableSet[F i] A) :
    MeasurableSpace.comap (Subtype.val : A → Ω) (H ⊔ ⨅ i, F i) =
      MeasurableSpace.comap (Subtype.val : A → Ω) H ⊔
        ⨅ i, MeasurableSpace.comap (Subtype.val : A → Ω) (F i) := by
  rw [MeasurableSpace.comap_sup, comap_subtype_iInf_of_measurable F A hA]

end LatticeProb
