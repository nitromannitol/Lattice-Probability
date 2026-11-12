import Mathlib
import LatticeProb.Prob.InterpolatedLawMeasurable

/-!
# Measurability of interpolated laws with random cells

In `LatticeProb.Prob.InterpolatedLawMeasurable` the covering sets `H k` were fixed and only the components `Q k`
depended on the parameter. Here the sets themselves depend measurably on a parameter `ω` (through their distance
functions `ω ↦ infDist z (H ω k)`), and the covering and local finiteness hypotheses of the interpolated law need
hold only for almost every `ω`.

* `measurable_weightedMixture`: a countable mixture, with measurable `ℝ≥0` weights, of Giry-measurable families
  of measures is Giry-measurable.
* `interpLawCMT`: the interpolated law as a continuous map `Z → ProbabilityMeasure E`, totalised by a constant
  map when the hypotheses fail.
* `aemeasurable_interpLawCMT`: under the almost sure hypotheses, `ω ↦ interpLawCMT (H ω) ε (Q · ω)` is
  almost everywhere measurable into `C(Z, ProbabilityMeasure E)`.
-/

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped ENNReal NNReal

namespace LatticeProb

section Mixture

variable {E : Type*} [MeasurableSpace E] {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]

/-- A mixture with measurable weights of measurable families of measures is measurable (for the
evaluation `σ`-algebra on measures). -/
theorem measurable_weightedMixture {c : ι → Ω → ℝ≥0} (hc : ∀ k, Measurable (c k))
    {Q : ι → Ω → Measure E} (hQ : ∀ k, Measurable (Q k)) :
    Measurable fun ω => weightedMixture (fun k => c k ω) (fun k => Q k ω) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have h : (fun ω => weightedMixture (fun k => c k ω) (fun k => Q k ω) s) =
      fun ω => ∑' k, (c k ω : ℝ≥0∞) * Q k ω s :=
    funext fun ω => weightedMixture_apply _ _ hs
  rw [h]
  exact Measurable.tsum fun k => (ENNReal.continuous_coe.measurable.comp (hc k)).mul
    ((Measure.measurable_coe hs).comp (hQ k))

end Mixture

section Interp

variable {Z : Type*} [PseudoMetricSpace Z] [SecondCountableTopology Z] {E : Type*}
  [TopologicalSpace E] [PseudoMetrizableSpace E] [SeparableSpace E] [MeasurableSpace E]
  [BorelSpace E] {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]

open Classical in
/-- The interpolated law as a continuous map, totalised: a constant map (the law `Q k₀`) if the local
finiteness or covering hypotheses fail. -/
noncomputable def interpLawCMT [Nonempty ι] (H : ι → Set Z) (ε : ℝ) (Q : ι → ProbabilityMeasure E) :
    C(Z, ProbabilityMeasure E) :=
  if h : (∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, interpWeight H ε k y ≠ 0}.Finite) ∧
      ∀ z, ∃ k, interpWeight H ε k z ≠ 0 then interpLawCM H ε h.1 h.2 Q
  else ContinuousMap.const Z (Q (Classical.arbitrary ι))

omit [SecondCountableTopology Z] [PseudoMetrizableSpace E] [SeparableSpace E] [Countable ι] in
theorem interpLawCMT_of_good [Nonempty ι] {H : ι → Set Z} {ε : ℝ}
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, interpWeight H ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k, interpWeight H ε k z ≠ 0) (Q : ι → ProbabilityMeasure E) :
    interpLawCMT H ε Q = interpLawCM H ε hloc hpos Q := by
  unfold interpLawCMT
  split_ifs with h
  · rfl
  · exact absurd ⟨hloc, hpos⟩ h

/-- The interpolated law with random cells is almost everywhere measurable, as a random element of the space of
continuous maps `Z → ProbabilityMeasure E`, if the distance functions of the cells and the components `Q k` are
measurable in the parameter and the covering and local finiteness hypotheses hold almost surely. -/
theorem aemeasurable_interpLawCMT [LocallyCompactSpace Z] [Nonempty ι] {P : Measure Ω}
    {H : Ω → ι → Set Z} {ε : ℝ} (hW : ∀ k z, Measurable fun ω => Metric.infDist z (H ω k))
    (hgood : ∀ᵐ ω ∂P,
      (∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, interpWeight (H ω) ε k y ≠ 0}.Finite) ∧
        ∀ z, ∃ k, interpWeight (H ω) ε k z ≠ 0)
    {Q : ι → Ω → ProbabilityMeasure E} (hQ : ∀ k, Measurable (Q k)) :
    AEMeasurable (fun ω => interpLawCMT (H ω) ε (fun k => Q k ω)) P := by
  classical
  set bad : Set Ω := {ω | ¬ ((∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, interpWeight (H ω) ε k y ≠ 0}.Finite) ∧
        ∀ z, ∃ k, interpWeight (H ω) ε k z ≠ 0)} with hbad
  have hbad0 : P bad = 0 := ae_iff.1 hgood
  set N : Set Ω := toMeasurable P bad with hNdef
  have hN : MeasurableSet N := measurableSet_toMeasurable _ _
  have hPN : P N = 0 := by rw [hNdef, measure_toMeasurable]; exact hbad0
  have hsub : bad ⊆ N := subset_toMeasurable _ _
  have hgoodN : ∀ ω, ω ∉ N → (∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, interpWeight (H ω) ε k y ≠ 0}.Finite) ∧
        ∀ z, ∃ k, interpWeight (H ω) ε k z ≠ 0 := fun ω hω => by
    by_contra h
    exact hω (hsub h)
  let F' : Ω → C(Z, ProbabilityMeasure E) := fun ω =>
    if ω ∈ N then ContinuousMap.const Z (Q (Classical.arbitrary ι) ω)
    else interpLawCMT (H ω) ε (fun k => Q k ω)
  have hF' : Measurable F' := by
    rw [ContinuousMap.measurable_iff_eval]
    intro z
    refine Measurable.subtype_mk ?_
    have hw : ∀ k, Measurable fun ω => interpWeight (H ω) ε k z := fun k =>
      measurable_real_toNNReal.comp (measurable_const.sub (hW k z))
    have hc : ∀ k, Measurable fun ω => normalizedWeight (interpWeight (H ω) ε) k z := fun k => by
      unfold normalizedWeight
      exact (hw k).div (Measurable.tsum hw)
    have hmix := measurable_weightedMixture hc (fun k => (measurable_subtype_coe.comp (hQ k)))
    have hconst : Measurable fun ω => ((Q (Classical.arbitrary ι) ω : ProbabilityMeasure E) : Measure E) :=
      measurable_subtype_coe.comp (hQ _)
    have heq : (fun ω => ((F' ω z : ProbabilityMeasure E) : Measure E)) = fun ω =>
        if ω ∈ N then ((Q (Classical.arbitrary ι) ω : ProbabilityMeasure E) : Measure E)
        else weightedMixture (fun k => normalizedWeight (interpWeight (H ω) ε) k z)
          (fun k => ((Q k ω : ProbabilityMeasure E) : Measure E)) := by
      funext ω
      by_cases hω : ω ∈ N
      · simp [F', hω]
      · obtain ⟨hl, hp⟩ := hgoodN ω hω
        simp only [F', hω, ↓reduceIte, interpLawCMT_of_good hl hp]
        rfl
    show Measurable fun ω => ((F' ω z : ProbabilityMeasure E) : Measure E)
    rw [heq]
    exact Measurable.ite hN hconst hmix
  refine ⟨F', hF', ?_⟩
  filter_upwards [compl_mem_ae_iff.2 hPN] with ω hω
  have hω' : ω ∉ N := hω
  simp [F', hω']

end Interp

end LatticeProb
