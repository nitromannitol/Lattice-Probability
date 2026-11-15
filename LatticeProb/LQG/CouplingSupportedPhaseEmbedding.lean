import LatticeProb.LQG.CouplingProductShiftedCellEmbedding
import LatticeProb.Prob.UniformModShift

/-! # Shifted cellular embeddings for supported phase laws -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT

/-- A phase law supported on the mesh interval gives a matching shifted
cellular embedding almost everywhere on the product space. -/
theorem ae_prod_shifted_cellularEmbedding_of_supported_phase
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ε : ℝ} (hε : 0 < ε) (Q : Measure ℝ) [SFinite Q] (hQ : Q ≪ volume)
    (hsupport : ∀ᵐ c ∂Q, c ∈ Icc (0 : ℝ) ε) :
    ∀ᵐ p ∂P.prod Q,
      let w : Path2 := ⟨fun t => bm p.1 (t + p.2),
        (bm p.1).continuous.comp (by fun_prop)⟩
      ∃ (hlf : IsLocallyFinite ε w)
        (H : CellularEmbedding (MatedCRT.graph ε w hlf) 0),
        H.cell = fun x : ℤ => (fun t => η p.1 (t + p.2)) ''
          Icc (ε * ((x : ℝ) - 1)) (ε * x) := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  have he := ae_prod_shifted_cellularEmbedding_of_coupling D hε Q hQ
  have hs := (Measure.quasiMeasurePreserving_snd (μ := P) (ν := Q)).ae hsupport
  filter_upwards [he, hs] with p hp hc
  exact hp hc.1 hc.2

/-- An independent uniform phase on one mesh interval gives a matching shifted
cellular embedding almost everywhere on the product space. -/
theorem ae_prod_shifted_cellularEmbedding_uniformIco
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ p ∂P.prod (LatticeProb.uniformIco ε),
      let w : Path2 := ⟨fun t => bm p.1 (t + p.2),
        (bm p.1).continuous.comp (by fun_prop)⟩
      ∃ (hlf : IsLocallyFinite ε w)
        (H : CellularEmbedding (MatedCRT.graph ε w hlf) 0),
        H.cell = fun x : ℤ => (fun t => η p.1 (t + p.2)) ''
          Icc (ε * ((x : ℝ) - 1)) (ε * x) := by
  let : IsProbabilityMeasure (LatticeProb.uniformIco ε) :=
    LatticeProb.isProbabilityMeasure_uniformIco hε
  apply ae_prod_shifted_cellularEmbedding_of_supported_phase D hε (LatticeProb.uniformIco ε)
  · exact ProbabilityTheory.cond_absolutelyContinuous
  · exact (ProbabilityTheory.ae_cond_mem (μ := volume) measurableSet_Ico).mono
      (fun _ hc => ⟨hc.1, le_of_lt hc.2⟩)

end MatedCRTHarmonic.MoTInput
