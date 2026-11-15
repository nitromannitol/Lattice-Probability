import LatticeProb.Topology.RandomShiftedCellThreeComponentsEvent

/-! # Simultaneous intersection component events for shifted curve cells -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace LatticeProb

/-- The event that every pair of shifted cells has at most two non-singleton
intersection components is null measurable under a finite measure. -/
theorem nullMeasurableSet_random_shifted_cell_all_inter_at_most_two_components
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω | ∀ k l : ℤ,
      let S : Set ℂ := (shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
        shiftedCompactCell (η ω) (ε ω) (θ ω) l
      ¬ ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S,
        connectedComponentIn S x ≠ connectedComponentIn S y ∧
        connectedComponentIn S x ≠ connectedComponentIn S z ∧
        connectedComponentIn S y ≠ connectedComponentIn S z ∧
        ¬ (connectedComponentIn S x).Subsingleton ∧
        ¬ (connectedComponentIn S y).Subsingleton ∧
        ¬ (connectedComponentIn S z).Subsingleton} μ := by
  have h := NullMeasurableSet.iInter (fun k : ℤ =>
    NullMeasurableSet.iInter (fun l : ℤ =>
      (nullMeasurableSet_random_shifted_cell_inter_three_components η ε θ k l hη hε hθ μ).compl))
  convert h using 1
  ext ω
  simp only [mem_iInter, mem_compl_iff, mem_ofPred_eq]

/-- The simultaneous event expressed using the corresponding curve segments. -/
theorem nullMeasurableSet_random_shifted_segment_all_inter_at_most_two_components
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω | ∀ k l : ℤ,
      let S : Set ℂ :=
        (η ω '' uIcc (ε ω * ((k : ℝ) - 1 + θ ω)) (ε ω * ((k : ℝ) + θ ω))) ∩
        (η ω '' uIcc (ε ω * ((l : ℝ) - 1 + θ ω)) (ε ω * ((l : ℝ) + θ ω)))
      ¬ ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S,
        connectedComponentIn S x ≠ connectedComponentIn S y ∧
        connectedComponentIn S x ≠ connectedComponentIn S z ∧
        connectedComponentIn S y ≠ connectedComponentIn S z ∧
        ¬ (connectedComponentIn S x).Subsingleton ∧
        ¬ (connectedComponentIn S y).Subsingleton ∧
        ¬ (connectedComponentIn S z).Subsingleton} μ := by
  simpa only [coe_shiftedCompactCell] using
    nullMeasurableSet_random_shifted_cell_all_inter_at_most_two_components η ε θ hη hε hθ μ

end LatticeProb
