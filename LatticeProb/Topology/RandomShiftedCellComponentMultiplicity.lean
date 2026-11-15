import LatticeProb.Topology.RandomShiftedCellTwoComponentsEvent

/-! # Multiplicity of components in random shifted cell intersections -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace LatticeProb

noncomputable local instance componentMultiplicityMeasurableSpace :
    MeasurableSpace (NonemptyCompacts ℂ) := borel _
local instance componentMultiplicityBorelSpace : BorelSpace (NonemptyCompacts ℂ) := ⟨rfl⟩

/-- The event that no component of the intersection of two random shifted cells
is non-singleton is null measurable. -/
theorem nullMeasurableSet_random_shifted_cell_inter_no_component
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ) (k l : ℤ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω | ∀ C ∈ connectedComponentIn
      ((shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
        shiftedCompactCell (η ω) (ε ω) (θ ω) l) ''
      ((shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
        shiftedCompactCell (η ω) (ε ω) (θ ω) l), C.Subsingleton} μ := by
  classical
  have hc (j : ℤ) : Measurable (fun ω => shiftedCompactCell (η ω) (ε ω) (θ ω) j) :=
    (measurable_shiftedCompactCell j).comp (hη.prodMk (hε.prodMk hθ))
  simpa only [Set.compl_ofPred, not_exists, not_and, not_not] using
    (nullMeasurableSet_random_complex_compact_inter_component
      _ _ (hc k) (hc l) μ).compl

/-- The event that the intersection of two random shifted cells has exactly one
non-singleton component is null measurable. -/
theorem nullMeasurableSet_random_shifted_cell_inter_unique_component
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ) (k l : ℤ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω | ∃! C, C ∈ connectedComponentIn
      ((shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
        shiftedCompactCell (η ω) (ε ω) (θ ω) l) ''
      ((shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
        shiftedCompactCell (η ω) (ε ω) (θ ω) l) ∧ ¬ C.Subsingleton} μ := by
  classical
  let S : Ω → Set ℂ := fun ω => (shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
    shiftedCompactCell (η ω) (ε ω) (θ ω) l
  let A : Set Ω := {ω | ∃ C ∈ connectedComponentIn (S ω) '' S ω, ¬ C.Subsingleton}
  let B : Set Ω := {ω | ∃ x ∈ S ω, ∃ y ∈ S ω,
    connectedComponentIn (S ω) x ≠ connectedComponentIn (S ω) y ∧
    ¬ (connectedComponentIn (S ω) x).Subsingleton ∧
    ¬ (connectedComponentIn (S ω) y).Subsingleton}
  have hc (j : ℤ) : Measurable (fun ω => shiftedCompactCell (η ω) (ε ω) (θ ω) j) :=
    (measurable_shiftedCompactCell j).comp (hη.prodMk (hε.prodMk hθ))
  have hA : NullMeasurableSet A μ :=
    nullMeasurableSet_random_complex_compact_inter_component _ _ (hc k) (hc l) μ
  have hB : NullMeasurableSet B μ :=
    nullMeasurableSet_random_shifted_cell_inter_two_components η ε θ k l hη hε hθ μ
  have heq : {ω : Ω | ∃! C, C ∈ connectedComponentIn (S ω) '' S ω ∧
      ¬ C.Subsingleton} = A ∩ Bᶜ := by
    ext ω
    constructor
    · rintro ⟨C, ⟨⟨x, hx, rfl⟩, hC⟩, hunique⟩
      refine ⟨⟨_, ⟨x, hx, rfl⟩, hC⟩, ?_⟩
      rintro ⟨u, hu, v, hv, hne, hsu, hsv⟩
      apply hne
      exact (hunique _ ⟨⟨u, hu, rfl⟩, hsu⟩).trans
        (hunique _ ⟨⟨v, hv, rfl⟩, hsv⟩).symm
    · rintro ⟨⟨C, ⟨x, hx, rfl⟩, hC⟩, hBω⟩
      refine ⟨_, ⟨⟨x, hx, rfl⟩, hC⟩, ?_⟩
      rintro D ⟨⟨y, hy, rfl⟩, hD⟩
      by_contra hne
      exact hBω ⟨y, hy, x, hx, hne, hD, hC⟩
  exact heq ▸ hA.inter hB.compl


/-- The zero-component event expressed using curve segment images. -/
theorem nullMeasurableSet_random_shifted_segment_inter_no_component
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ) (k l : ℤ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω | ∀ C ∈ connectedComponentIn
      ((η ω '' uIcc (ε ω * ((k : ℝ) - 1 + θ ω)) (ε ω * ((k : ℝ) + θ ω))) ∩
        (η ω '' uIcc (ε ω * ((l : ℝ) - 1 + θ ω)) (ε ω * ((l : ℝ) + θ ω)))) ''
      ((η ω '' uIcc (ε ω * ((k : ℝ) - 1 + θ ω)) (ε ω * ((k : ℝ) + θ ω))) ∩
        (η ω '' uIcc (ε ω * ((l : ℝ) - 1 + θ ω)) (ε ω * ((l : ℝ) + θ ω)))),
      C.Subsingleton} μ := by
  simpa only [coe_shiftedCompactCell] using
    nullMeasurableSet_random_shifted_cell_inter_no_component η ε θ k l hη hε hθ μ

/-- The unique-component event expressed using curve segment images. -/
theorem nullMeasurableSet_random_shifted_segment_inter_unique_component
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ) (k l : ℤ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω | ∃! C, C ∈ connectedComponentIn
      ((η ω '' uIcc (ε ω * ((k : ℝ) - 1 + θ ω)) (ε ω * ((k : ℝ) + θ ω))) ∩
        (η ω '' uIcc (ε ω * ((l : ℝ) - 1 + θ ω)) (ε ω * ((l : ℝ) + θ ω)))) ''
      ((η ω '' uIcc (ε ω * ((k : ℝ) - 1 + θ ω)) (ε ω * ((k : ℝ) + θ ω))) ∩
        (η ω '' uIcc (ε ω * ((l : ℝ) - 1 + θ ω)) (ε ω * ((l : ℝ) + θ ω)))) ∧
      ¬ C.Subsingleton} μ := by
  simpa only [coe_shiftedCompactCell] using
    nullMeasurableSet_random_shifted_cell_inter_unique_component η ε θ k l hη hε hθ μ

end LatticeProb
