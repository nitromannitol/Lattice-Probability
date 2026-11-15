import LatticeProb.LQG.CouplingShiftedCellEmbedding
import LatticeProb.Topology.RandomShiftedCellComponentCount

/-! # Component counts of shifted coupled curve cells -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT

/-- Each coupled curve has an almost-everywhere measurable array of shifted
cell intersection component counts, with diagonal entries set to zero. -/
theorem aemeasurable_shifted_component_counts_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (ε θ : Ω → ℝ) (hε : AEMeasurable ε P) (hθ : AEMeasurable θ P) :
    ∀ f ∈ ({ηL, η, η₀} : Set (Ω → C(ℝ, ℂ))),
      AEMeasurable (fun ω (k l : ℤ) => if k = l then 0 else
        (LatticeProb.nonSingletonComponents
          ((LatticeProb.shiftedCompactCell (f ω) (ε ω) (θ ω) k : Set ℂ) ∩
            LatticeProb.shiftedCompactCell (f ω) (ε ω) (θ ω) l)).ncard) P := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  intro f hf
  have hfm : Measurable f := by
    simp only [mem_insert_iff, mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl
    · exact D.measurable_curves.1
    · exact D.measurable_curves.2.1
    · exact D.measurable_curves.2.2.1
  exact LatticeProb.aemeasurable_shifted_cell_component_array_of_ae f ε θ P
    hfm.aemeasurable hε hθ

end MatedCRTHarmonic.MoTInput
