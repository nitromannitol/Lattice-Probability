import LatticeProb.MeasureTheory.MeasureDenseProfileFamily

/-!
# Separability of measurable profiles for Borel measures

The integrated truncated-distance topology on measurable profiles is separable when the
reference measure is finite and the domain and label spaces are second countable.
-/

set_option autoImplicit false

open MeasureTheory TopologicalSpace

namespace LatticeProb.MeasurableProfile

/-- Measurable profiles over a finite Borel measure form a separable pseudometric space. -/
theorem separableSpace_of_borel {α E : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α]
    [PseudoEMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] (μ : Measure α) [IsFiniteMeasure μ] :
    @SeparableSpace (MeasurableProfile (E := E) μ)
      (instPseudoMetricSpace μ).toUniformSpace.toTopologicalSpace := by
  obtain ⟨D, hDc, hD⟩ := exists_countable_dense E
  obtain ⟨_, _, _, _, h⟩ := exists_countable_dense_simple_profiles μ hDc hD
  exact ⟨⟨_, h⟩⟩

end LatticeProb.MeasurableProfile
