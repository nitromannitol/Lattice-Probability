import LatticeProb.MeasureTheory.MeasurableProfileSeparable

/-! # Separability of measurable-profile subspaces -/

open Set MeasureTheory TopologicalSpace

namespace LatticeProb.MeasurableProfile

/-- Every subspace of the measurable-profile pseudometric space is separable under countable
approximation assumptions. -/
theorem subtype_separableSpace_of_countable_measureDense_algebra
    {α E : Type*} [MeasurableSpace α] [PseudoEMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E]
    (μ : Measure α) [IsFiniteMeasure μ]
    {D : Set E} (hDc : D.Countable) (hD : Dense D)
    {𝒜 : Set (Set α)} (hAc : 𝒜.Countable) (h𝒜 : IsSetAlgebra 𝒜)
    (hA : μ.MeasureDense 𝒜) (V : Set (MeasurableProfile (E := E) μ)) :
    SeparableSpace V := by
  let : SeparableSpace (MeasurableProfile (E := E) μ) :=
    separableSpace_of_countable_measureDense_algebra μ hDc hD hAc h𝒜 hA
  infer_instance

end LatticeProb.MeasurableProfile
