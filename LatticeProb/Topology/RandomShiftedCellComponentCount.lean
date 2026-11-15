import LatticeProb.Topology.ComplexCompactComponentCount

/-! # Component counts of almost-everywhere measurable shifted cells -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace LatticeProb

/-- The exact array of component counts is almost everywhere measurable when
its curve, mesh and phase are almost everywhere measurable. -/
theorem aemeasurable_shifted_cell_component_ncard_array_of_ae
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hη : AEMeasurable η μ) (hε : AEMeasurable ε μ) (hθ : AEMeasurable θ μ) :
    AEMeasurable (fun ω (k l : ℤ) => (nonSingletonComponents
      ((shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
        shiftedCompactCell (η ω) (ε ω) (θ ω) l)).ncard) μ := by
  let η' := hη.mk η
  let ε' := hε.mk ε
  let θ' := hθ.mk θ
  apply (aemeasurable_shifted_cell_component_ncard_array η' ε' θ'
    hη.measurable_mk hε.measurable_mk hθ.measurable_mk μ).congr
  filter_upwards [hη.ae_eq_mk, hε.ae_eq_mk, hθ.ae_eq_mk] with ω hηω hεω hθω
  simp only [η', ε', θ', ← hηω, ← hεω, ← hθω]

/-- Setting diagonal counts to zero preserves almost-everywhere measurability. -/
theorem aemeasurable_shifted_cell_component_array_of_ae
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hη : AEMeasurable η μ) (hε : AEMeasurable ε μ) (hθ : AEMeasurable θ μ) :
    AEMeasurable (fun ω (k l : ℤ) => if k = l then 0 else
      (nonSingletonComponents ((shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
        shiftedCompactCell (η ω) (ε ω) (θ ω) l)).ncard) μ := by
  apply AEMeasurable.of_eval
  intro k
  apply AEMeasurable.of_eval
  intro l
  by_cases h : k = l
  · simp only [h, ite_true]
    exact aemeasurable_const
  · simp only [h, ite_false]
    exact ((aemeasurable_shifted_cell_component_ncard_array_of_ae η ε θ μ hη hε hθ).eval k).eval l

end LatticeProb
