import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.Rat.Cast.Order

/-! # Measurable endpoints from countable visits -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- If measurable rational-time visits lie between two endpoints and approach each endpoint,
then both endpoints are measurable. -/
theorem measurable_endpoints_of_rational_visits
    {Ω : Type*} [MeasurableSpace Ω] (visit : Ω → ℚ → Prop) (a b : Ω → ℝ)
    (hvisit : ∀ q, MeasurableSet {ω | visit ω q})
    (hbound : ∀ ω q, visit ω q → a ω ≤ q ∧ (q : ℝ) ≤ b ω)
    (hleft : ∀ ω t, a ω < t → ∃ q : ℚ, visit ω q ∧ (q : ℝ) < t)
    (hright : ∀ ω t, t < b ω → ∃ q : ℚ, visit ω q ∧ t < (q : ℝ)) :
    Measurable a ∧ Measurable b := by
  constructor
  · apply measurable_of_Iio
    intro t
    have heq : a ⁻¹' Iio t = ⋃ q : {q : ℚ // (q : ℝ) < t}, {ω | visit ω q.1} := by
      ext ω
      simp only [mem_preimage, mem_Iio, mem_iUnion, mem_ofPred_eq]
      constructor
      · intro h
        obtain ⟨q, hq, hqt⟩ := hleft ω t h
        exact ⟨⟨q, hqt⟩, hq⟩
      · rintro ⟨q, hq⟩
        exact lt_of_le_of_lt (hbound ω q.1 hq).1 q.2
    rw [heq]
    exact MeasurableSet.iUnion fun q => hvisit q.1
  · apply measurable_of_Ioi
    intro t
    have heq : b ⁻¹' Ioi t = ⋃ q : {q : ℚ // t < (q : ℝ)}, {ω | visit ω q.1} := by
      ext ω
      simp only [mem_preimage, mem_Ioi, mem_iUnion, mem_ofPred_eq]
      constructor
      · intro h
        obtain ⟨q, hq, htq⟩ := hright ω t h
        exact ⟨⟨q, htq⟩, hq⟩
      · rintro ⟨q, hq⟩
        exact lt_of_lt_of_le q.2 (hbound ω q.1 hq).2
    rw [heq]
    exact MeasurableSet.iUnion fun q => hvisit q.1

end LatticeProb
