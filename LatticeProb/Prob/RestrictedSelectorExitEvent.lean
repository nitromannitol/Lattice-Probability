import LatticeProb.Prob.SelectorEventCoupling

/-! # Exit events for restricted selectors -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- A selector active on a set becomes inactive exactly outside that set when
restricted to it. -/
theorem restrictSelector_none_iff_not_mem {X J : Type*} (U : Set X)
    (f : X → Option J) (hactive : ∀ x ∈ U, f x ≠ none) (x : X) :
    restrictSelector U f x = none ↔ x ∉ U := by
  classical
  constructor
  · exact restrictSelector_none_not_mem U f hactive
  · intro hx
    simp only [restrictSelector, ite_eq_right hx]

/-- The disagreement mass of two restricted selectors bounds the difference
between the endpoint probabilities of leaving their respective active sets. -/
theorem restrictedSelector_exit_event_le_of_coupling
    {X Y J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (π : Measure (X × Y)) (U : Set X) (V : Set Y)
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (f : X → Option J) (g : Y → Option J)
    (hf : ∀ x ∈ U, f x ≠ none) (hg : ∀ y ∈ V, g y ≠ none) :
    π.fst Uᶜ ≤ π.snd Vᶜ +
        π {p | restrictSelector U f p.1 ≠ restrictSelector V g p.2} ∧
    π.snd Vᶜ ≤ π.fst Uᶜ +
        π {p | restrictSelector U f p.1 ≠ restrictSelector V g p.2} := by
  have hpreU : restrictSelector U f ⁻¹' {none} = Uᶜ := by
    ext x
    exact restrictSelector_none_iff_not_mem U f hf x
  have hpreV : restrictSelector V g ⁻¹' {none} = Vᶜ := by
    ext y
    exact restrictSelector_none_iff_not_mem V g hg y
  have h := selector_event_le_of_coupling π (restrictSelector U f)
    (restrictSelector V g) {none} (hpreU ▸ hU.compl) (hpreV ▸ hV.compl)
  simpa only [hpreU, hpreV] using h

end LatticeProb
