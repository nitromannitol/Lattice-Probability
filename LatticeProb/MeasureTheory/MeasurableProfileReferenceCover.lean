import LatticeProb.MeasureTheory.MeasurableProfileSeparable
import LatticeProb.MeasureTheory.SeparableReferenceCover

/-! # Countable reference covers for measurable profiles -/

open Set MeasureTheory TopologicalSpace

namespace LatticeProb.MeasurableProfile

/-- The full measurable-profile space is separable under countable approximation
assumptions, and a nonempty separable family of valid profiles admits a countable
reference cover when discrepancy is dominated by integrated distance. The separability
assumption on the valid family is separate from that of the full profile space. -/
theorem separableSpace_and_exists_countable_reference_cover
    {α E Y : Type*} [MeasurableSpace α] [PseudoEMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E]
    (μ : Measure α) [IsFiniteMeasure μ]
    {D : Set E} (hDc : D.Countable) (hD : Dense D)
    {𝒜 : Set (Set α)} (hAc : 𝒜.Countable) (h𝒜 : IsSetAlgebra 𝒜)
    (hA : μ.MeasureDense 𝒜) (V : Set (MeasurableProfile (E := E) μ))
    (hVsep : SeparableSpace V) (hV : V.Nonempty)
    (q : MeasurableProfile (E := E) μ → Y) (δ : Y → Y → ℝ)
    (hδ : ∀ f ∈ V, ∀ g ∈ V, δ (q f) (q g) ≤ (integralDist μ f g).toReal) :
    SeparableSpace (MeasurableProfile (E := E) μ) ∧
      ∃ r : ℕ → MeasurableProfile (E := E) μ, (∀ n, r n ∈ V) ∧
        ∀ f ∈ V, ∀ ε > 0, ∃ n, δ (q (r n)) (q f) < ε := by
  refine ⟨separableSpace_of_countable_measureDense_algebra μ hDc hD hAc h𝒜 hA, ?_⟩
  let : SeparableSpace V := hVsep
  exact LatticeProb.exists_countable_reference_cover V hV q δ hδ

end LatticeProb.MeasurableProfile
