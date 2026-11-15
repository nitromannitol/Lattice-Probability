import LatticeProb.Topology.RandomShiftedCellComponentArray

/-! # Exact shifted-cell counts from fixed-pair bounds -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace LatticeProb

/-- Fixed-pair almost-sure bounds suffice for almost-everywhere measurability of
    the exact component-count array with zero diagonal. -/
theorem aemeasurable_shifted_cell_component_array_of_pairwise
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (h : ∀ k l : ℤ, k ≠ l → ∀ᵐ ω ∂μ,
      let S : Set ℂ := (shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
        shiftedCompactCell (η ω) (ε ω) (θ ω) l
      ¬ ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S,
        connectedComponentIn S x ≠ connectedComponentIn S y ∧
        connectedComponentIn S x ≠ connectedComponentIn S z ∧
        connectedComponentIn S y ≠ connectedComponentIn S z ∧
        ¬ (connectedComponentIn S x).Subsingleton ∧
        ¬ (connectedComponentIn S y).Subsingleton ∧
        ¬ (connectedComponentIn S z).Subsingleton) :
    AEMeasurable (fun ω (k l : ℤ) => if k = l then 0 else
      (nonSingletonComponents ((shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
        shiftedCompactCell (η ω) (ε ω) (θ ω) l)).ncard) μ := by
  classical
  apply AEMeasurable.of_eval
  intro k
  apply AEMeasurable.of_eval
  intro l
  by_cases hkl : k = l
  · simpa only [hkl, ite_true] using (aemeasurable_const : AEMeasurable (fun _ : Ω => (0 : ℕ)) μ)
  · simp only [hkl, ite_false]
    apply ((aemeasurable_shifted_cell_truncated_component_array η ε θ hη hε hθ μ).eval k |>.eval l).congr
    filter_upwards [h k l hkl] with ω hω
    apply truncatedComponentCount_eq_ncard
    rintro A ⟨⟨x, hx, rfl⟩, hA⟩ B ⟨⟨y, hy, rfl⟩, hB⟩ C ⟨⟨z, hz, rfl⟩, hC⟩ hAB hAC hBC
    exact hω ⟨x, hx, y, hy, z, hz, hAB, hAC, hBC, hA, hB, hC⟩

end LatticeProb
