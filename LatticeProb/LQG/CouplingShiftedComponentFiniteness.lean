import LatticeProb.LQG.CouplingShiftedCellEmbedding
import LatticeProb.Topology.RandomShiftedCellFiniteComponents

/-! # Finiteness events for shifted coupled curve cells -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT

/-- The extended component counts for each coupled curve retain infinite
component families and form an almost-everywhere measurable array. -/
theorem aemeasurable_shifted_component_encards_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (ε θ : Ω → ℝ) (hε : AEMeasurable ε P) (hθ : AEMeasurable θ P) :
    ∀ f ∈ ({ηL, η, η₀} : Set (Ω → C(ℝ, ℂ))),
      AEMeasurable (fun ω (k l : ℤ) =>
        (LatticeProb.nonSingletonComponents
          ((LatticeProb.shiftedCompactCell (f ω) (ε ω) (θ ω) k : Set ℂ) ∩
            LatticeProb.shiftedCompactCell (f ω) (ε ω) (θ ω) l)).encard) P := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  intro f hf
  have hfm : Measurable f := by
    simp only [mem_insert_iff, mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl
    · exact D.measurable_curves.1
    · exact D.measurable_curves.2.1
    · exact D.measurable_curves.2.2.1
  exact LatticeProb.aemeasurable_shifted_cell_component_encard_array f ε θ P
    hfm.aemeasurable hε hθ

/-- The event of finite component families for every pair of shifted cells
of each coupled curve is null measurable. -/
theorem nullMeasurableSet_coupled_shifted_cell_all_finite_components
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (ε θ : Ω → ℝ) (hε : AEMeasurable ε P) (hθ : AEMeasurable θ P) :
    NullMeasurableSet {ω : Ω | ∀ f ∈ ({ηL, η, η₀} : Set (Ω → C(ℝ, ℂ))),
      ∀ k l : ℤ, (LatticeProb.nonSingletonComponents
        ((LatticeProb.shiftedCompactCell (f ω) (ε ω) (θ ω) k : Set ℂ) ∩
          LatticeProb.shiftedCompactCell (f ω) (ε ω) (θ ω) l)).Finite} P := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hfinite (f : Ω → C(ℝ, ℂ)) (hf : Measurable f) :=
    LatticeProb.nullMeasurableSet_shifted_cell_all_finite_components f ε θ P
      hf.aemeasurable hε hθ
  have h := (hfinite ηL D.measurable_curves.1).inter
    ((hfinite η D.measurable_curves.2.1).inter (hfinite η₀ D.measurable_curves.2.2.1))
  convert h using 1
  ext ω
  simp only [mem_ofPred_eq, mem_inter_iff, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
    forall_eq]

end MatedCRTHarmonic.MoTInput
