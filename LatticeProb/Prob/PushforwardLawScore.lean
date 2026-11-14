import LatticeProb.Prob.ProbabilityMeasureBorel

/-! # Measurability of scores of pushforward probability laws -/

set_option autoImplicit false
set_option maxHeartbeats 400000

open MeasureTheory Topology TopologicalSpace

namespace LatticeProb

/-- Pushforward by a measurable map is measurable on spaces of probability measures equipped
with their evaluation σ-algebras. -/
theorem measurable_probabilityMeasure_map {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    {f : A → E} (hf : Measurable f) :
    Measurable (fun μ : ProbabilityMeasure A => μ.map f) := by
  refine Measurable.subtype_mk ?_
  exact (Measure.measurable_map f hf).comp measurable_subtype_coe

/-- A Lévy–Prokhorov score against a continuous family of reference laws is jointly
measurable, even when the map used to push the other law forward is only measurable. -/
theorem measurable_levyProkhorovDist_map {Z A E : Type*} [TopologicalSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace A]
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SeparableSpace E]
    {f : A → E} (hf : Measurable f) {β : Z → ProbabilityMeasure E} (hβ : Continuous β) :
    Measurable (fun p : Z × ProbabilityMeasure A =>
      levyProkhorovDist (β p.1 : Measure E) (p.2.map f : Measure E)) := by
  let : SecondCountableTopology (LevyProkhorov (ProbabilityMeasure E)) :=
    (LevyProkhorov.probabilityMeasureHomeomorph (Ω := E)).symm.secondCountableTopology
  let : MeasurableSpace (LevyProkhorov (ProbabilityMeasure E)) := borel _
  let : BorelSpace (LevyProkhorov (ProbabilityMeasure E)) := ⟨rfl⟩
  have hβ' : Measurable (fun z => LevyProkhorov.ofMeasure (β z)) :=
    (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp hβ).measurable
  have hf' : Measurable (fun μ : ProbabilityMeasure A =>
      LevyProkhorov.ofMeasure (μ.map f)) :=
    LevyProkhorov.continuous_ofMeasure_probabilityMeasure.measurable.comp
      (measurable_probabilityMeasure_map hf)
  have h := (hβ'.comp measurable_fst).dist (hf'.comp measurable_snd)
  simpa only [LevyProkhorov.dist_probabilityMeasure_def, Function.comp_apply] using h

/-- For a fixed law, the Lévy–Prokhorov score is continuous in the reference parameter. -/
theorem continuous_levyProkhorovDist_map {Z A E : Type*} [TopologicalSpace Z]
    [MeasurableSpace A] [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SeparableSpace E] (f : A → E) {β : Z → ProbabilityMeasure E} (hβ : Continuous β)
    (μ : ProbabilityMeasure A) :
    Continuous (fun z => levyProkhorovDist (β z : Measure E) (μ.map f : Measure E)) := by
  have h : Continuous (fun z => dist (LevyProkhorov.ofMeasure (β z))
      (LevyProkhorov.ofMeasure (μ.map f))) :=
    (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp hβ).dist continuous_const
  simpa only [LevyProkhorov.dist_probabilityMeasure_def, Function.comp_apply] using h

end LatticeProb
