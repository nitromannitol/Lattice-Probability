import LatticeProb.Prob.PartitionDyadicChoice

/-! # Restriction of selectors to a measurable set -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- A selector that is inactive outside a specified set. -/
noncomputable def restrictSelector {X J : Type*} (outer : Set X)
    (f : X → Option J) (x : X) : Option J :=
  by
    classical
    exact if x ∈ outer then f x else none

lemma measurable_restrictSelector {X J : Type*} [MeasurableSpace X]
    [MeasurableSpace (Option J)] (outer : Set X) (f : X → Option J)
    (houter : MeasurableSet outer) (hf : Measurable f) :
    Measurable (restrictSelector outer f) := by
  classical
  change Measurable (fun x => if x ∈ outer then f x else none)
  exact Measurable.ite houter hf measurable_const

lemma restrictSelector_some {X J : Type*} (outer : Set X) (f : X → Option J)
    {x : X} {j : J} (h : restrictSelector outer f x = some j) :
    x ∈ outer ∧ f x = some j := by
  classical
  by_cases hx : x ∈ outer
  · exact ⟨hx, by simpa only [restrictSelector, ite_eq_left hx] using h⟩
  · simp [restrictSelector, hx] at h

lemma restrictSelector_none_not_mem {X J : Type*} (outer : Set X) (f : X → Option J)
    (hactive : ∀ x ∈ outer, f x ≠ none) {x : X}
    (h : restrictSelector outer f x = none) : x ∉ outer := by
  classical
  intro hx
  exact hactive x hx (by simpa only [restrictSelector, ite_eq_left hx] using h)

lemma frontier_restrictSelector_fiber_subset {X J : Type*} [TopologicalSpace X]
    (outer : Set X) (f : X → Option J) (q : Option J) :
    frontier (restrictSelector outer f ⁻¹' {q}) ⊆
      frontier outer ∪ frontier (f ⁻¹' {q}) := by
  classical
  cases q with
  | none =>
    have heq : restrictSelector outer f ⁻¹' {none} = outerᶜ ∪ f ⁻¹' {none} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_union, mem_compl_iff, restrictSelector]
      by_cases hx : x ∈ outer <;> simp [hx]
    rw [heq]
    intro x hx
    rcases frontier_union_subset outerᶜ (f ⁻¹' {none}) hx with h | h
    · exact Or.inl (by simpa only [frontier_compl] using h.1)
    · exact Or.inr h.2
  | some j =>
    have heq : restrictSelector outer f ⁻¹' {some j} = outer ∩ f ⁻¹' {some j} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, restrictSelector]
      by_cases hx : x ∈ outer <;> simp [hx]
    rw [heq]
    intro x hx
    rcases frontier_inter_subset outer (f ⁻¹' {some j}) hx with h | h
    · exact Or.inl h.1
    · exact Or.inr h.2

lemma measure_frontier_restrictSelector_fiber {X J : Type*}
    [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X)
    (outer : Set X) (f : X → Option J) (q : Option J)
    (houter : μ (frontier outer) = 0) (hf : μ (frontier (f ⁻¹' {q})) = 0) :
    μ (frontier (restrictSelector outer f ⁻¹' {q})) = 0 :=
  measure_mono_null (frontier_restrictSelector_fiber_subset outer f q)
    (measure_union_null houter hf)

end LatticeProb
