import LatticeProb.MeasureTheory.MeasurableProfileValidReferenceCover
import LatticeProb.MeasureTheory.CountableReferenceMeasurability

/-! # Scalar measurability from valid profile reference tests -/

open Set MeasureTheory TopologicalSpace

namespace LatticeProb.MeasurableProfile

/-- Measurable discrepancy tests and a uniform scalar bound imply measurability
of an observable on values represented by valid measurable profiles. -/
theorem measurable_scalar_of_valid_reference_tests
    {α E Y Ω : Type*} [MeasurableSpace α] [PseudoEMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    (μ : Measure α) [IsFiniteMeasure μ]
    {D : Set E} (hDc : D.Countable) (hD : Dense D)
    {𝒜 : Set (Set α)} (hAc : 𝒜.Countable) (h𝒜 : IsSetAlgebra 𝒜)
    (hA : μ.MeasureDense 𝒜) (V : Set (MeasurableProfile (E := E) μ))
    (hV : V.Nonempty) (q : MeasurableProfile (E := E) μ → Y) (δ : Y → Y → ℝ)
    (hδ : ∀ f ∈ V, ∀ g ∈ V, δ (q f) (q g) ≤ (integralDist μ f g).toReal)
    (z : Ω → Y) (F : Y → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hz : ∀ ω, ∃ g ∈ V, q g = z ω)
    (htest : ∀ f ∈ V, Measurable fun ω => δ (q f) (z ω))
    (hbound : ∀ f ∈ V, ∀ g ∈ V, |F (q g) - F (q f)| ≤ C * δ (q f) (q g)) :
    Measurable (fun ω => F (z ω)) := by
  obtain ⟨_, r, hr, hcover⟩ :=
    separableSpace_and_exists_countable_valid_reference_cover μ hDc hD hAc h𝒜 hA V hV q δ hδ
  apply LatticeProb.measurable_of_countable_reference_discrepancies
    (fun ω => F (z ω)) (fun n => F (q (r n))) (fun n ω => δ (q (r n)) (z ω)) C hC
  · exact fun n => htest (r n) (hr n)
  · intro n ω
    obtain ⟨g, hg, hq⟩ := hz ω
    rw [← hq]
    exact hbound (r n) (hr n) g hg
  · intro ω ε hε
    obtain ⟨g, hg, hq⟩ := hz ω
    obtain ⟨n, hn⟩ := hcover g hg ε hε
    exact ⟨n, hq ▸ hn⟩

end LatticeProb.MeasurableProfile
