import LatticeProb.Topology.RandomShiftedCellPairwiseExactArray

/-! # Component counts for almost-everywhere measurable shifted cells -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace LatticeProb

/-- Almost-everywhere measurable curve, mesh, and phase inputs give an
almost-everywhere measurable component-count array, provided that each distinct
pair almost surely has at most two non-singleton intersection components. -/
theorem aemeasurable_shifted_cell_component_array_of_pairwise_ae
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hη : AEMeasurable η μ) (hε : AEMeasurable ε μ) (hθ : AEMeasurable θ μ)
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
  let η' := hη.mk η
  let ε' := hε.mk ε
  let θ' := hθ.mk θ
  have h' : ∀ k l : ℤ, k ≠ l → ∀ᵐ ω ∂μ,
      let S : Set ℂ := (shiftedCompactCell (η' ω) (ε' ω) (θ' ω) k : Set ℂ) ∩
        shiftedCompactCell (η' ω) (ε' ω) (θ' ω) l
      ¬ ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S,
        connectedComponentIn S x ≠ connectedComponentIn S y ∧
        connectedComponentIn S x ≠ connectedComponentIn S z ∧
        connectedComponentIn S y ≠ connectedComponentIn S z ∧
        ¬ (connectedComponentIn S x).Subsingleton ∧
        ¬ (connectedComponentIn S y).Subsingleton ∧
        ¬ (connectedComponentIn S z).Subsingleton := by
    intro k l hkl
    filter_upwards [h k l hkl, hη.ae_eq_mk, hε.ae_eq_mk, hθ.ae_eq_mk] with ω hh hηω hεω hθω
    simpa only [η', ε', θ', ← hηω, ← hεω, ← hθω] using hh
  apply (aemeasurable_shifted_cell_component_array_of_pairwise η' ε' θ'
    hη.measurable_mk hε.measurable_mk hθ.measurable_mk μ h').congr
  filter_upwards [hη.ae_eq_mk, hε.ae_eq_mk, hθ.ae_eq_mk] with ω hηω hεω hθω
  simp only [η', ε', θ', ← hηω, ← hεω, ← hθω]

end LatticeProb
