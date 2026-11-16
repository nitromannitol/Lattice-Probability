import LatticeProb.MeasureTheory.MeasurableProfileReferenceCover
import LatticeProb.MeasureTheory.MeasurableProfileSubtypeSeparable

/-! # Reference covers for valid measurable profiles -/

open Set MeasureTheory TopologicalSpace

namespace LatticeProb.MeasurableProfile

/-- Under countable approximation assumptions, the measurable-profile space is separable
and every nonempty family of valid profiles has a countable reference cover when
its discrepancy is dominated by integrated distance. -/
theorem separableSpace_and_exists_countable_valid_reference_cover
    {α E Y : Type*} [MeasurableSpace α] [PseudoEMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E]
    (μ : Measure α) [IsFiniteMeasure μ]
    {D : Set E} (hDc : D.Countable) (hD : Dense D)
    {𝒜 : Set (Set α)} (hAc : 𝒜.Countable) (h𝒜 : IsSetAlgebra 𝒜)
    (hA : μ.MeasureDense 𝒜) (V : Set (MeasurableProfile (E := E) μ))
    (hV : V.Nonempty) (q : MeasurableProfile (E := E) μ → Y) (δ : Y → Y → ℝ)
    (hδ : ∀ f ∈ V, ∀ g ∈ V, δ (q f) (q g) ≤ (integralDist μ f g).toReal) :
    SeparableSpace (MeasurableProfile (E := E) μ) ∧
      ∃ r : ℕ → MeasurableProfile (E := E) μ, (∀ n, r n ∈ V) ∧
        ∀ f ∈ V, ∀ ε > 0, ∃ n, δ (q (r n)) (q f) < ε := by
  exact separableSpace_and_exists_countable_reference_cover μ hDc hD hAc h𝒜 hA V
    (subtype_separableSpace_of_countable_measureDense_algebra μ hDc hD hAc h𝒜 hA V)
    hV q δ hδ

end LatticeProb.MeasurableProfile
