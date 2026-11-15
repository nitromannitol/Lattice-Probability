import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Bases

/-! # Almost-everywhere predicates on open unions -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- On a second-countable space, a predicate holding almost everywhere on each
open set of an arbitrary family holds almost everywhere on their union. -/
theorem ae_restrict_iUnion_of_isOpen
    {α ι : Type*} [TopologicalSpace α] [SecondCountableTopology α] [MeasurableSpace α]
    (μ : Measure α) (U : ι → Set α) (p : α → Prop)
    (hopen : ∀ i, IsOpen (U i))
    (hae : ∀ i, ∀ᵐ x ∂(μ.restrict (U i)), p x) :
    ∀ᵐ x ∂(μ.restrict (⋃ i, U i)), p x := by
  obtain ⟨T, hT, hU⟩ := TopologicalSpace.isOpen_iUnion_countable U hopen
  rw [← hU, ae_restrict_biUnion_iff U hT p]
  exact fun i _ => hae i

/-- A locally almost-everywhere predicate holds almost everywhere on the set
covered by its open witnessing neighborhoods. -/
theorem ae_restrict_of_locally_ae
    {α : Type*} [TopologicalSpace α] [SecondCountableTopology α] [MeasurableSpace α]
    (μ : Measure α) (s : Set α) (p : α → Prop)
    (hlocal : ∀ x ∈ s, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ U ⊆ s ∧
      ∀ᵐ y ∂(μ.restrict U), p y) :
    ∀ᵐ y ∂(μ.restrict s), p y := by
  let ι := {U : Set α // IsOpen U ∧ U ⊆ s ∧ ∀ᵐ y ∂(μ.restrict U), p y}
  have hs : (⋃ U : ι, (U : Set α)) = s := by
    apply Subset.antisymm
    · exact iUnion_subset fun U => U.2.2.1
    · intro x hx
      obtain ⟨U, hU, hxU, hUs, hpU⟩ := hlocal x hx
      exact mem_iUnion.mpr ⟨⟨U, hU, hUs, hpU⟩, hxU⟩
  rw [← hs]
  exact ae_restrict_iUnion_of_isOpen μ (fun U : ι => U.1) p
    (fun U => U.2.1) (fun U => U.2.2.2)

end LatticeProb
