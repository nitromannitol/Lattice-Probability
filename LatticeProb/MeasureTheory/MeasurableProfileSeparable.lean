import LatticeProb.MeasureTheory.CountableProfileDensity

/-! # Separability of measurable profiles -/

open Set MeasureTheory TopologicalSpace

namespace LatticeProb.MeasurableProfile

/-- The space of almost-everywhere measurable profiles is separable for the integrated
truncated-distance pseudometric when there are countable dense labels and a countable
measure-dense set algebra. -/
theorem separableSpace_of_countable_measureDense_algebra {α E : Type*} [MeasurableSpace α]
    [PseudoEMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] (μ : Measure α) [IsFiniteMeasure μ]
    {D : Set E} (hDc : D.Countable) (hD : Dense D)
    {𝒜 : Set (Set α)} (hAc : 𝒜.Countable) (h𝒜 : IsSetAlgebra 𝒜)
    (hA : μ.MeasureDense 𝒜) :
    @SeparableSpace (MeasurableProfile (E := E) μ)
      (instPseudoMetricSpace μ).toUniformSpace.toTopologicalSpace := by
  exact ⟨⟨_, countable_dense_simple_profiles μ hDc hD hAc h𝒜 hA⟩⟩

end LatticeProb.MeasurableProfile
