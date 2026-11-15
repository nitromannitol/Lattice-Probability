import LatticeProb.LQG.CouplingShiftedCellEmbedding

/-! # Shifted cellular embeddings at countably many meshes -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT

/-- For countably many positive meshes and fixed absolutely continuous phase laws,
    almost every coupling sample has shifted cellular embeddings at almost every
    phase for each mesh. -/
theorem ae_countable_shifted_cellularEmbedding_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ι : Type} [Countable ι] (ε : ι → ℝ) (hε : ∀ i, 0 < ε i)
    (Q : ι → Measure ℝ) (hQ : ∀ i, Q i ≪ volume)
    (hQmem : ∀ i, ∀ᵐ c ∂Q i, c ∈ Icc 0 (ε i)) :
    ∀ᵐ ω ∂P, ∀ i, ∀ᵐ c ∂Q i,
      ∃ (hlf : IsLocallyFinite (ε i)
          ⟨fun t => bm ω (t + c), (bm ω).continuous.comp (by fun_prop)⟩)
        (H : CellularEmbedding (MatedCRT.graph (ε i)
          ⟨fun t => bm ω (t + c), (bm ω).continuous.comp (by fun_prop)⟩ hlf) 0),
        H.cell = fun x : ℤ => (fun t => η ω (t + c)) ''
          Icc (ε i * ((x : ℝ) - 1)) (ε i * x) := by
  refine ae_all_iff.2 fun i => ?_
  filter_upwards [ae_shifted_cellularEmbedding_of_coupling D (hε i)] with ω hω
  filter_upwards [(hQ i).ae_le hω, hQmem i] with c hc hmem
  exact hc hmem.1 hmem.2

end MatedCRTHarmonic.MoTInput
