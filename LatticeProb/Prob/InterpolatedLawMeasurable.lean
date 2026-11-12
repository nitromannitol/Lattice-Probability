import Mathlib
import LatticeProb.Prob.InterpolatedLaw
import LatticeProb.Prob.ProbabilityMeasureBorel

/-!
# Measurability of interpolated laws

A countable mixture with fixed weights of Giry-measurable families of probability measures is
Giry-measurable. Consequently, if the components `Q k ω` of an interpolated law depend measurably
on a parameter `ω`, the interpolated law, viewed as a continuous map from the base space to the
space of probability measures, is a Borel random element of that function space.
-/

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped ENNReal NNReal

namespace LatticeProb

section Mixture

variable {E : Type*} [MeasurableSpace E] {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]

/-- A mixture with fixed weights of measurable families of probability measures is measurable
(for the evaluation `σ`-algebra on probability measures). -/
theorem measurable_weightedMixturePM {c : ι → ℝ≥0} (hc : HasSum c 1)
    {Q : ι → Ω → ProbabilityMeasure E} (hQ : ∀ k, Measurable (Q k)) :
    Measurable fun ω => weightedMixturePM hc (fun k => Q k ω) := by
  refine Measurable.subtype_mk ?_
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have h : (fun ω => weightedMixture c (fun k => (Q k ω : Measure E)) s) =
      fun ω => ∑' k, (c k : ℝ≥0∞) * (Q k ω : Measure E) s :=
    funext fun ω => weightedMixture_apply c _ hs
  rw [h]
  exact Measurable.tsum fun k => measurable_const.mul
    ((Measure.measurable_coe hs).comp (measurable_subtype_coe.comp (hQ k)))

end Mixture

section Interp

variable {Z : Type*} [PseudoMetricSpace Z] [SecondCountableTopology Z] {E : Type*}
  [TopologicalSpace E] [PseudoMetrizableSpace E] [SeparableSpace E] [MeasurableSpace E]
  [BorelSpace E] {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]

/-- The interpolated law as a continuous map from the base space to probability measures. -/
noncomputable def interpLawCM (H : ι → Set Z) (ε : ℝ)
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, interpWeight H ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k, interpWeight H ε k z ≠ 0) (Q : ι → ProbabilityMeasure E) :
    C(Z, ProbabilityMeasure E) :=
  ⟨interpLaw H ε hloc hpos Q, continuous_interpLaw hloc hpos Q⟩

/-- If the components `Q k ω` are measurable in the parameter `ω`, the interpolated law is a
Borel random element of the space of continuous maps from the base space to probability
measures. -/
theorem measurable_interpLawCM [LocallyCompactSpace Z] (H : ι → Set Z) (ε : ℝ)
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, interpWeight H ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k, interpWeight H ε k z ≠ 0) {Q : ι → Ω → ProbabilityMeasure E}
    (hQ : ∀ k, Measurable (Q k)) :
    Measurable fun ω => interpLawCM H ε hloc hpos (fun k => Q k ω) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro z
  exact measurable_weightedMixturePM (hasSum_normalizedWeight hloc hpos z) hQ

end Interp

end LatticeProb
