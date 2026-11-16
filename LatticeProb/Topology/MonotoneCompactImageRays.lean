import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Separation.Hausdorff

/-! # Open rays in monotone compact images -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A continuous monotone surjection from a compact ordered space to a Hausdorff
space has open rays in the target, even if its topology is not initially known
to be the order topology. -/
theorem isOpen_rays_of_monotone_compact_surjection
    {A B : Type*} [LinearOrder A] [TopologicalSpace A] [OrderTopology A] [CompactSpace A]
    [LinearOrder B] [TopologicalSpace B] [T2Space B]
    {f : A → B} (hcont : Continuous f) (hsurj : Function.Surjective f)
    (hmono : Monotone f) :
    (∀ b : B, IsOpen (Iio b)) ∧ (∀ b : B, IsOpen (Ioi b)) := by
  have hclosed : ∀ b : B, IsClosed (Ici b) ∧ IsClosed (Iic b) := by
    intro b
    obtain ⟨a, rfl⟩ := hsurj b
    have hIci : f '' Ici a = Ici (f a) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hmono hx
      · intro hy
        obtain ⟨x, rfl⟩ := hsurj y
        by_cases hax : a ≤ x
        · exact ⟨x, hax, rfl⟩
        · have h : f x = f a := le_antisymm (hmono (le_of_not_ge hax)) hy
          exact ⟨a, le_rfl, h.symm⟩
    have hIic : f '' Iic a = Iic (f a) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hmono hx
      · intro hy
        obtain ⟨x, rfl⟩ := hsurj y
        by_cases hxa : x ≤ a
        · exact ⟨x, hxa, rfl⟩
        · have h : f x = f a := le_antisymm hy (hmono (le_of_not_ge hxa))
          exact ⟨a, le_rfl, h.symm⟩
    exact ⟨hIci ▸ hcont.isClosedMap _ isClosed_Ici,
      hIic ▸ hcont.isClosedMap _ isClosed_Iic⟩
  constructor
  · intro b
    simpa only [compl_Ici] using (hclosed b).1.isOpen_compl
  · intro b
    simpa only [compl_Iic] using (hclosed b).2.isOpen_compl

end LatticeProb
