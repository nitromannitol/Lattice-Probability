import LatticeProb.Topology.ComponentVisitEndpointVersions

/-! # Endpoint versions from visits before a fixed time -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Rational visits before a fixed cutoff determine measurable versions of the
endpoints when the visits approximate both endpoints and the right endpoint lies
before the cutoff. -/
theorem exists_measurable_endpoints_of_ae_rational_visits_before
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (s : ℝ)
    (visit : Ω → ℚ → Prop) (a b : Ω → ℝ)
    (hvisit : ∀ q : ℚ, (q : ℝ) < s → MeasurableSet {ω | visit ω q})
    (hgood : ∀ᵐ ω ∂P,
      b ω < s ∧
      (∀ q, visit ω q → a ω ≤ q ∧ (q : ℝ) ≤ b ω) ∧
      (∀ t, a ω < t → ∃ q : ℚ, visit ω q ∧ (q : ℝ) < t) ∧
      (∀ t, t < b ω → ∃ q : ℚ, visit ω q ∧ t < (q : ℝ))) :
    ∃ a' b' : Ω → ℝ, Measurable a' ∧ Measurable b' ∧
      (∀ᵐ ω ∂P, a' ω = a ω ∧ b' ω = b ω) := by
  let V : Ω → ℚ → Prop := fun ω q => visit ω q ∧ (q : ℝ) < s
  apply exists_measurable_endpoints_of_ae_rational_visits P V a b
  · intro q
    by_cases hq : (q : ℝ) < s
    · simpa only [V, hq, and_true] using hvisit q hq
    · simpa only [V, hq, and_false, ofPred_false] using MeasurableSet.empty
  · filter_upwards [hgood] with ω hω
    have hv : ∀ q, visit ω q → (q : ℝ) < s :=
      fun q hq => lt_of_le_of_lt ((hω.2.1 q hq).2) hω.1
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      exact hω.2.1 q hq.1
    · intro t ht
      obtain ⟨q, hq, hqt⟩ := hω.2.2.1 t ht
      exact ⟨q, ⟨hq, hv q hq⟩, hqt⟩
    · intro t ht
      obtain ⟨q, hq, htq⟩ := hω.2.2.2 t ht
      exact ⟨q, ⟨hq, hv q hq⟩, htq⟩

/-- For an open region traced over an interval ending before a fixed cutoff,
measurable rational visits before the cutoff give measurable endpoint versions. -/
theorem exists_measurable_endpoints_of_ae_open_curve_visits_before
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [PerfectSpace E]
    (P : Measure Ω) (s : ℝ) (η : Ω → ℝ → E) (U : Ω → Set E) (a b : Ω → ℝ)
    (hvisit : ∀ q : ℚ, (q : ℝ) < s → MeasurableSet {ω | η ω q ∈ U ω})
    (hgood : ∀ᵐ ω ∂P, b ω < s ∧ Continuous (η ω) ∧ IsOpen (U ω) ∧
      (U ω).Nonempty ∧ η ω '' Icc (a ω) (b ω) = closure (U ω) ∧
      ∀ᵐ t ∂volume, η ω t ∈ U ω ↔ t ∈ Ioo (a ω) (b ω)) :
    ∃ a' b' : Ω → ℝ, Measurable a' ∧ Measurable b' ∧
      (∀ᵐ ω ∂P, a' ω = a ω ∧ b' ω = b ω) := by
  apply exists_measurable_endpoints_of_ae_rational_visits_before P s
    (fun ω q => η ω q ∈ U ω) a b hvisit
  filter_upwards [hgood] with ω hω
  refine ⟨hω.1, ?_⟩
  exact rational_visits_of_open_ae_interval volume (η ω ⁻¹' U ω) (a ω) (b ω)
    (hω.2.2.1.preimage hω.2.1)
    (interval_lt_of_image_eq_closure_open (η ω) (U ω) (a ω) (b ω)
      hω.2.2.1 hω.2.2.2.1 hω.2.2.2.2.1) hω.2.2.2.2.2

end LatticeProb
