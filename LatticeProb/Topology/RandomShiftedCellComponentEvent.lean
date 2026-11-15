import LatticeProb.Topology.ComplexCompactComponentEvent

/-! # Components of intersections of random shifted curve cells -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace LatticeProb

noncomputable local instance : MeasurableSpace (NonemptyCompacts ℂ) := borel _
local instance : BorelSpace (NonemptyCompacts ℂ) := ⟨rfl⟩

/-- For measurable random curves, meshes and shifts, the event that the intersection
of two labelled shifted cells has a non-singleton component is null measurable. -/
theorem nullMeasurableSet_random_shifted_cell_inter_component
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ) (k l : ℤ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω | ∃ C ∈ connectedComponentIn
      ((shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
        shiftedCompactCell (η ω) (ε ω) (θ ω) l) ''
      ((shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
        shiftedCompactCell (η ω) (ε ω) (θ ω) l), ¬ C.Subsingleton} μ := by
  have hc (j : ℤ) : Measurable (fun ω => shiftedCompactCell (η ω) (ε ω) (θ ω) j) :=
    (measurable_shiftedCompactCell j).comp (hη.prodMk (hε.prodMk hθ))
  exact nullMeasurableSet_random_complex_compact_inter_component _ _ (hc k) (hc l) μ

/-- The same event expressed as intersections of the corresponding segment images. -/
theorem nullMeasurableSet_random_shifted_segment_inter_component
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ) (k l : ℤ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω | ∃ C ∈ connectedComponentIn
      ((η ω '' uIcc (ε ω * ((k : ℝ) - 1 + θ ω)) (ε ω * ((k : ℝ) + θ ω))) ∩
        (η ω '' uIcc (ε ω * ((l : ℝ) - 1 + θ ω)) (ε ω * ((l : ℝ) + θ ω)))) ''
      ((η ω '' uIcc (ε ω * ((k : ℝ) - 1 + θ ω)) (ε ω * ((k : ℝ) + θ ω))) ∩
        (η ω '' uIcc (ε ω * ((l : ℝ) - 1 + θ ω)) (ε ω * ((l : ℝ) + θ ω)))),
      ¬ C.Subsingleton} μ := by
  simpa only [coe_shiftedCompactCell] using
    nullMeasurableSet_random_shifted_cell_inter_component η ε θ k l hη hε hθ μ

end LatticeProb
