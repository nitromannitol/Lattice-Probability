import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! # Measurable selected-neighborhood events -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- The event that two points share an active selector and both belong to the
selected measurable set is measurable. -/
theorem measurableSet_common_selected_neighborhood
    {X J : Type*} [MeasurableSpace X] [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (f : X → Option J) (hf : Measurable f) (G : J → Set X)
    (hG : ∀ j, MeasurableSet (G j)) :
    MeasurableSet {p : X × X | ∃ j, f p.1 = some j ∧ f p.2 = some j ∧
      p.1 ∈ G j ∧ p.2 ∈ G j} := by
  have h : ∀ j, MeasurableSet (f ⁻¹' {some j} ∩ G j) :=
    fun j => (hf (measurableSet_singleton (some j))).inter (hG j)
  convert MeasurableSet.iUnion (fun j => (h j).prod (h j)) using 1
  ext p
  simp only [mem_ofPred_eq, mem_iUnion, mem_prod, mem_inter_iff, mem_preimage,
    mem_singleton_iff]
  tauto

/-- The failure of two points to share a selected measurable neighborhood is
measurable. -/
theorem measurableSet_not_common_selected_neighborhood
    {X J : Type*} [MeasurableSpace X] [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (f : X → Option J) (hf : Measurable f) (G : J → Set X)
    (hG : ∀ j, MeasurableSet (G j)) :
    MeasurableSet {p : X × X | ¬ ∃ j, f p.1 = some j ∧ f p.2 = some j ∧
      p.1 ∈ G j ∧ p.2 ∈ G j} :=
  (measurableSet_common_selected_neighborhood f hf G hG).compl

end LatticeProb
