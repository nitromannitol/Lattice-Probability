import LatticeProb.Topology.RandomShiftedCellExtendedComponentCount

/-! # Finiteness of shifted-cell intersection components -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- The event that every pair of shifted cells has finitely many non-singleton
intersection components is null measurable. -/
theorem nullMeasurableSet_shifted_cell_all_finite_components
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hη : AEMeasurable η μ) (hε : AEMeasurable ε μ) (hθ : AEMeasurable θ μ) :
    NullMeasurableSet {ω : Ω | ∀ k l : ℤ, (nonSingletonComponents
      ((shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
        shiftedCompactCell (η ω) (ε ω) (θ ω) l)).Finite} μ := by
  have ha := aemeasurable_shifted_cell_component_encard_array η ε θ μ hη hε hθ
  have hh := NullMeasurableSet.iInter (fun k : ℤ =>
    NullMeasurableSet.iInter (fun l : ℤ =>
      (((ha.eval k).eval l).nullMeasurableSet_preimage (MeasurableSet.singleton ⊤)).compl))
  convert hh using 1
  ext ω
  simp only [mem_ofPred_eq, mem_iInter, mem_compl_iff, mem_preimage, mem_singleton_iff,
    Set.encard_ne_top_iff]

end LatticeProb
