import LatticeProb.Topology.ComplexThreeCompactComponentsEvent

/-! # Three components of intersections of random shifted curve cells -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace LatticeProb

noncomputable local instance shiftedThreeMeasurableSpace :
    MeasurableSpace (NonemptyCompacts ℂ) := borel _
local instance shiftedThreeBorelSpace : BorelSpace (NonemptyCompacts ℂ) := ⟨rfl⟩

/-- Three distinct non-singleton components in the intersection of two random
shifted cells form a null-measurable event. -/
theorem nullMeasurableSet_random_shifted_cell_inter_three_components
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ) (k l : ℤ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω |
      let S : Set ℂ := (shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
        shiftedCompactCell (η ω) (ε ω) (θ ω) l
      ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S,
        connectedComponentIn S x ≠ connectedComponentIn S y ∧
        connectedComponentIn S x ≠ connectedComponentIn S z ∧
        connectedComponentIn S y ≠ connectedComponentIn S z ∧
        ¬ (connectedComponentIn S x).Subsingleton ∧
        ¬ (connectedComponentIn S y).Subsingleton ∧
        ¬ (connectedComponentIn S z).Subsingleton} μ := by
  have hc (j : ℤ) : Measurable (fun ω => shiftedCompactCell (η ω) (ε ω) (θ ω) j) :=
    (measurable_shiftedCompactCell j).comp (hη.prodMk (hε.prodMk hθ))
  exact nullMeasurableSet_random_complex_compact_inter_three_components _ _ (hc k) (hc l) μ

/-- The three-component event expressed using the corresponding curve segments. -/
theorem nullMeasurableSet_random_shifted_segment_inter_three_components
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ) (k l : ℤ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω |
      let S : Set ℂ :=
        (η ω '' uIcc (ε ω * ((k : ℝ) - 1 + θ ω)) (ε ω * ((k : ℝ) + θ ω))) ∩
        (η ω '' uIcc (ε ω * ((l : ℝ) - 1 + θ ω)) (ε ω * ((l : ℝ) + θ ω)))
      ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S,
        connectedComponentIn S x ≠ connectedComponentIn S y ∧
        connectedComponentIn S x ≠ connectedComponentIn S z ∧
        connectedComponentIn S y ≠ connectedComponentIn S z ∧
        ¬ (connectedComponentIn S x).Subsingleton ∧
        ¬ (connectedComponentIn S y).Subsingleton ∧
        ¬ (connectedComponentIn S z).Subsingleton} μ := by
  simpa only [coe_shiftedCompactCell] using
    nullMeasurableSet_random_shifted_cell_inter_three_components η ε θ k l hη hε hθ μ

end LatticeProb
