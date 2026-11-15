import LatticeProb.Topology.ComplexTwoCompactComponentsEvent

/-! # Two components of intersections of random shifted curve cells -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace LatticeProb

noncomputable local instance : MeasurableSpace (NonemptyCompacts ℂ) := borel _
local instance : BorelSpace (NonemptyCompacts ℂ) := ⟨rfl⟩

/-- Two distinct non-singleton components in the intersection of two random
shifted cells form a null-measurable event. -/
theorem nullMeasurableSet_random_shifted_cell_inter_two_components
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ) (k l : ℤ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω |
      ∃ x ∈ (shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
          shiftedCompactCell (η ω) (ε ω) (θ ω) l,
      ∃ y ∈ (shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
          shiftedCompactCell (η ω) (ε ω) (θ ω) l,
        connectedComponentIn ((shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
            shiftedCompactCell (η ω) (ε ω) (θ ω) l) x ≠
          connectedComponentIn ((shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
            shiftedCompactCell (η ω) (ε ω) (θ ω) l) y ∧
        ¬ (connectedComponentIn ((shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
            shiftedCompactCell (η ω) (ε ω) (θ ω) l) x).Subsingleton ∧
        ¬ (connectedComponentIn ((shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
            shiftedCompactCell (η ω) (ε ω) (θ ω) l) y).Subsingleton} μ := by
  have hc (j : ℤ) : Measurable (fun ω => shiftedCompactCell (η ω) (ε ω) (θ ω) j) :=
    (measurable_shiftedCompactCell j).comp (hη.prodMk (hε.prodMk hθ))
  exact nullMeasurableSet_random_complex_compact_inter_two_components _ _ (hc k) (hc l) μ

/-- The two-component event expressed using the corresponding curve segments. -/
theorem nullMeasurableSet_random_shifted_segment_inter_two_components
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ) (k l : ℤ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω |
      ∃ x ∈ (η ω '' uIcc (ε ω * ((k : ℝ) - 1 + θ ω)) (ε ω * ((k : ℝ) + θ ω))) ∩
          (η ω '' uIcc (ε ω * ((l : ℝ) - 1 + θ ω)) (ε ω * ((l : ℝ) + θ ω))),
      ∃ y ∈ (η ω '' uIcc (ε ω * ((k : ℝ) - 1 + θ ω)) (ε ω * ((k : ℝ) + θ ω))) ∩
          (η ω '' uIcc (ε ω * ((l : ℝ) - 1 + θ ω)) (ε ω * ((l : ℝ) + θ ω))),
        connectedComponentIn ((η ω '' uIcc (ε ω * ((k : ℝ) - 1 + θ ω))
              (ε ω * ((k : ℝ) + θ ω))) ∩
            (η ω '' uIcc (ε ω * ((l : ℝ) - 1 + θ ω))
              (ε ω * ((l : ℝ) + θ ω)))) x ≠
          connectedComponentIn ((η ω '' uIcc (ε ω * ((k : ℝ) - 1 + θ ω))
              (ε ω * ((k : ℝ) + θ ω))) ∩
            (η ω '' uIcc (ε ω * ((l : ℝ) - 1 + θ ω))
              (ε ω * ((l : ℝ) + θ ω)))) y ∧
        ¬ (connectedComponentIn ((η ω '' uIcc (ε ω * ((k : ℝ) - 1 + θ ω))
              (ε ω * ((k : ℝ) + θ ω))) ∩
            (η ω '' uIcc (ε ω * ((l : ℝ) - 1 + θ ω))
              (ε ω * ((l : ℝ) + θ ω)))) x).Subsingleton ∧
        ¬ (connectedComponentIn ((η ω '' uIcc (ε ω * ((k : ℝ) - 1 + θ ω))
              (ε ω * ((k : ℝ) + θ ω))) ∩
            (η ω '' uIcc (ε ω * ((l : ℝ) - 1 + θ ω))
              (ε ω * ((l : ℝ) + θ ω)))) y).Subsingleton} μ := by
  simpa only [coe_shiftedCompactCell] using
    nullMeasurableSet_random_shifted_cell_inter_two_components η ε θ k l hη hε hθ μ

end LatticeProb
