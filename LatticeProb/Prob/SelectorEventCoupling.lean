import LatticeProb.Prob.SelectorRestrictionCoupling

/-! # Event bounds from selector couplings -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- A coupling bounds the difference between the probabilities of any event
observed through two selectors by their disagreement mass. -/
theorem selector_event_le_of_coupling
    {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (π : Measure (X × Y)) (f : X → Z) (g : Y → Z) (A : Set Z)
    (hf : MeasurableSet (f ⁻¹' A)) (hg : MeasurableSet (g ⁻¹' A)) :
    π.fst (f ⁻¹' A) ≤ π.snd (g ⁻¹' A) + π {p | f p.1 ≠ g p.2} ∧
    π.snd (g ⁻¹' A) ≤ π.fst (f ⁻¹' A) + π {p | f p.1 ≠ g p.2} := by
  constructor
  · rw [Measure.fst_apply hf, Measure.snd_apply hg]
    calc
      π (Prod.fst ⁻¹' (f ⁻¹' A)) ≤
          π ((Prod.snd ⁻¹' (g ⁻¹' A)) ∪ {p | f p.1 ≠ g p.2}) := by
        apply measure_mono
        intro p hp
        by_cases h : f p.1 = g p.2
        · apply Or.inl
          change g p.2 ∈ A
          change f p.1 ∈ A at hp
          exact h ▸ hp
        · exact Or.inr h
      _ ≤ π (Prod.snd ⁻¹' (g ⁻¹' A)) + π {p | f p.1 ≠ g p.2} :=
        measure_union_le _ _
  · rw [Measure.fst_apply hf, Measure.snd_apply hg]
    calc
      π (Prod.snd ⁻¹' (g ⁻¹' A)) ≤
          π ((Prod.fst ⁻¹' (f ⁻¹' A)) ∪ {p | f p.1 ≠ g p.2}) := by
        apply measure_mono
        intro p hp
        by_cases h : f p.1 = g p.2
        · apply Or.inl
          change f p.1 ∈ A
          change g p.2 ∈ A at hp
          exact h.symm ▸ hp
        · exact Or.inr h
      _ ≤ π (Prod.fst ⁻¹' (f ⁻¹' A)) + π {p | f p.1 ≠ g p.2} :=
        measure_union_le _ _

end LatticeProb
