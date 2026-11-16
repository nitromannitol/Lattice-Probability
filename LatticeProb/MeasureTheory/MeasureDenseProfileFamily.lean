import LatticeProb.MeasureTheory.MeasureDenseAlgebra
import LatticeProb.MeasureTheory.CountableProfileDensity

/-!
# Countable dense simple profiles from a measure-dense algebra

For a finite separable reference measure, a countable measure-dense set algebra exists
(`LatticeProb.exists_countable_measureDense_algebra`). Feeding it to
`LatticeProb.MeasurableProfile.countable_dense_simple_profiles` gives a countable dense family of
measurable simple profiles with labels in a prescribed countable dense set.

* `exists_countable_dense_simple_profiles_of_isSeparable`: the statement for a finite measure on
  an arbitrary measurable space, under the separability hypothesis `IsSeparable μ`.
* `exists_countable_dense_simple_profiles`: the statement for a finite Borel measure on a
  second-countable topological space, where separability holds automatically.
-/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace LatticeProb.MeasurableProfile

/-- For a finite separable measure and a countable dense set of labels `D`, there is a countable
measure-dense set algebra `𝒜` such that the simple profiles with values in `D` and fibres in `𝒜`
form a countable dense family of measurable profiles. -/
theorem exists_countable_dense_simple_profiles_of_isSeparable {α E : Type*}
    [MeasurableSpace α] [PseudoEMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] (μ : Measure α) [IsFiniteMeasure μ] [IsSeparable μ]
    {D : Set E} (hDc : D.Countable) (hD : Dense D) :
    ∃ 𝒜 : Set (Set α), 𝒜.Countable ∧ IsSetAlgebra 𝒜 ∧ μ.MeasureDense 𝒜 ∧
      let family : Set (SimpleFunc α E) := {f | Set.range f ⊆ D ∧
        ∀ y ∈ Set.range f, f ⁻¹' {y} ∈ 𝒜}
      let profiles := (fun f : SimpleFunc α E =>
        (⟨f, f.measurable.aemeasurable⟩ : MeasurableProfile (E := E) μ)) '' family
      profiles.Countable ∧
        @Dense _ (instPseudoMetricSpace μ).toUniformSpace.toTopologicalSpace profiles := by
  obtain ⟨𝒜, hAc, h𝒜, hA⟩ := exists_countable_measureDense_algebra μ
  exact ⟨𝒜, hAc, h𝒜, hA, countable_dense_simple_profiles μ hDc hD hAc h𝒜 hA⟩

/-- For a finite Borel measure on a second-countable topological space and a countable dense set
of labels `D`, there is a countable measure-dense set algebra `𝒜` such that the simple profiles
with values in `D` and fibres in `𝒜` form a countable dense family of measurable profiles. -/
theorem exists_countable_dense_simple_profiles {α E : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α]
    [PseudoEMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] (μ : Measure α) [IsFiniteMeasure μ]
    {D : Set E} (hDc : D.Countable) (hD : Dense D) :
    ∃ 𝒜 : Set (Set α), 𝒜.Countable ∧ IsSetAlgebra 𝒜 ∧ μ.MeasureDense 𝒜 ∧
      let family : Set (SimpleFunc α E) := {f | Set.range f ⊆ D ∧
        ∀ y ∈ Set.range f, f ⁻¹' {y} ∈ 𝒜}
      let profiles := (fun f : SimpleFunc α E =>
        (⟨f, f.measurable.aemeasurable⟩ : MeasurableProfile (E := E) μ)) '' family
      profiles.Countable ∧
        @Dense _ (instPseudoMetricSpace μ).toUniformSpace.toTopologicalSpace profiles :=
  exists_countable_dense_simple_profiles_of_isSeparable μ hDc hD

end LatticeProb.MeasurableProfile
