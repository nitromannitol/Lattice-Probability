import LatticeProb.Topology.PlanarInvarianceOfDomain

/-! Ambient interiors of homeomorphic subspaces of the plane. -/

set_option autoImplicit false

noncomputable section

open Set Topology

namespace LatticeProb

/-- A homeomorphism between planar subspaces maps ambient interior points to
ambient interior points. -/
theorem homeomorph_subspace_mem_interior {A B : Set ℂ} (e : A ≃ₜ B)
    (x : A) (hx : x.1 ∈ interior A) : (e x).1 ∈ interior B := by
  classical
  let f : ℂ → ℂ := fun z => if h : z ∈ A then (e ⟨z, h⟩).1 else 0
  have hf : ContinuousOn f (interior A) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun z : interior A => (e ⟨z.1, interior_subset z.2⟩).1) := by
      exact continuous_subtype_val.comp (e.continuous.comp
        (continuous_subtype_val.subtype_mk _))
    convert hc using 1
    funext z
    simp [f, interior_subset z.2]
  have hi : InjOn f (interior A) := by
    intro a ha b hb hab
    have haA := interior_subset ha
    have hbA := interior_subset hb
    simp only [f, dite_eq_left haA, dite_eq_left hbA] at hab
    exact congrArg Subtype.val (e.injective (Subtype.ext hab))
  have hopen : IsOpen (f '' interior A) :=
    isOpen_image_of_continuousOn_injOn isOpen_interior hf hi
  have hsub : f '' interior A ⊆ B := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [f, dite_eq_left (interior_subset hz)]
    exact (e ⟨z, interior_subset hz⟩).2
  have him : f x.1 ∈ f '' interior A := ⟨x.1, hx, rfl⟩
  have := interior_maximal hsub hopen him
  simpa [f, x.2] using this

/-- A homeomorphism between planar subspaces preserves ambient interior membership. -/
theorem homeomorph_subspace_mem_interior_iff {A B : Set ℂ} (e : A ≃ₜ B)
    (x : A) : x.1 ∈ interior A ↔ (e x).1 ∈ interior B := by
  constructor
  · exact homeomorph_subspace_mem_interior e x
  · intro hx
    simpa only [Homeomorph.symm_apply_apply] using
      homeomorph_subspace_mem_interior e.symm (e x) hx

end LatticeProb
