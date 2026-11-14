import LatticeProb.Prob.ProbabilityMeasureBorel

/-! # Measurability of the distance between probability measures -/

set_option autoImplicit false

open MeasureTheory Topology TopologicalSpace

namespace LatticeProb

/-- The Lévy–Prokhorov distance between two measurable families of probability measures is
measurable. -/
theorem measurable_levyProkhorovDist {X E : Type*} [MeasurableSpace X]
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SeparableSpace E]
    {μ ν : X → ProbabilityMeasure E} (hμ : Measurable μ) (hν : Measurable ν) :
    Measurable (fun x => levyProkhorovDist (μ x : Measure E) (ν x : Measure E)) := by
  let : SecondCountableTopology (LevyProkhorov (ProbabilityMeasure E)) :=
    (LevyProkhorov.probabilityMeasureHomeomorph (Ω := E)).symm.secondCountableTopology
  let : MeasurableSpace (LevyProkhorov (ProbabilityMeasure E)) := borel _
  let : BorelSpace (LevyProkhorov (ProbabilityMeasure E)) := ⟨rfl⟩
  have hμ' : Measurable (fun x => LevyProkhorov.ofMeasure (μ x)) :=
    LevyProkhorov.continuous_ofMeasure_probabilityMeasure.measurable.comp hμ
  have hν' : Measurable (fun x => LevyProkhorov.ofMeasure (ν x)) :=
    LevyProkhorov.continuous_ofMeasure_probabilityMeasure.measurable.comp hν
  simpa only [LevyProkhorov.dist_probabilityMeasure_def] using hμ'.dist hν'

/-- The Lévy–Prokhorov distance is jointly measurable on probability measures. -/
theorem measurable_levyProkhorovDist_pair {E : Type*}
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SeparableSpace E] :
    Measurable (fun p : ProbabilityMeasure E × ProbabilityMeasure E =>
      levyProkhorovDist (p.1 : Measure E) (p.2 : Measure E)) :=
  measurable_levyProkhorovDist measurable_fst measurable_snd

end LatticeProb
