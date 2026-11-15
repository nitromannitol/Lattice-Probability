import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent

/-! # Interior images under conformal maps -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- An injective holomorphic map on the interior of a set sends that interior
into the interior of any set containing the image. -/
theorem image_interior_subset_interior_of_differentiableOn_injOn
    {A B : Set ℂ} {f : ℂ → ℂ}
    (hmap : MapsTo f A B)
    (hdiff : DifferentiableOn ℂ f (interior A))
    (hinj : InjOn f (interior A)) :
    f '' interior A ⊆ interior B := by
  apply interior_maximal ?_ (QuantumZipper.CA.isOpen_image_of_injOn' isOpen_interior hdiff hinj)
  rintro _ ⟨x, hx, rfl⟩
  exact hmap (interior_subset hx)

end LatticeProb
