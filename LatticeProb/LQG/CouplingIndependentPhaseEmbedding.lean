import LatticeProb.LQG.CouplingSupportedPhaseEmbedding
import Mathlib.Probability.Independence.Basic

/-! # Shifted embeddings under an independent phase -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter ProbabilityTheory
open scoped NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT

/-- A product-law realization inherits the supported-phase embedding event. -/
theorem ae_shifted_cellularEmbedding_of_product_law
    {γ : ℝ} {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {R : Measure Ξ}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ε : ℝ} (hε : 0 < ε) (Q : Measure ℝ) [SFinite Q] (hQ : Q ≪ volume)
    (hsupport : ∀ᵐ c ∂Q, c ∈ Icc (0 : ℝ) ε)
    (S : Ξ → Ω) (T : Ξ → ℝ) (hS : Measurable S) (hT : Measurable T)
    (hlaw : R.map (fun ξ => (S ξ, T ξ)) = P.prod Q) :
    ∀ᵐ ξ ∂(R),
      let w : Path2 := ⟨fun t => bm (S ξ) (t + T ξ),
        (bm (S ξ)).continuous.comp (by fun_prop)⟩
      ∃ (hlf : IsLocallyFinite ε w)
        (H : CellularEmbedding (MatedCRT.graph ε w hlf) 0),
        H.cell = fun x : ℤ => (fun t => η (S ξ) (t + T ξ)) ''
          Icc (ε * ((x : ℝ) - 1)) (ε * x) := by
  have hp : Measure.QuasiMeasurePreserving (fun ξ => (S ξ, T ξ)) R (P.prod Q) := by
    refine ⟨hS.prodMk hT, ?_⟩
    rw [hlaw]
  exact hp.ae (ae_prod_shifted_cellularEmbedding_of_supported_phase D hε Q hQ hsupport)

/-- An independent uniform phase on a realization gives the shifted embedding. -/
theorem ae_shifted_cellularEmbedding_of_independent_uniform
    {γ : ℝ} {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {R : Measure Ξ} [IsProbabilityMeasure R]
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ε : ℝ} (hε : 0 < ε)
    (S : Ξ → Ω) (T : Ξ → ℝ) (hS : Measurable S) (hT : Measurable T)
    (hS_law : R.map S = P) (hT_law : R.map T = LatticeProb.uniformIco ε)
    (hind : IndepFun S T R) :
    ∀ᵐ ξ ∂(R),
      let w : Path2 := ⟨fun t => bm (S ξ) (t + T ξ),
        (bm (S ξ)).continuous.comp (by fun_prop)⟩
      ∃ (hlf : IsLocallyFinite ε w)
        (H : CellularEmbedding (MatedCRT.graph ε w hlf) 0),
        H.cell = fun x : ℤ => (fun t => η (S ξ) (t + T ξ)) ''
          Icc (ε * ((x : ℝ) - 1)) (ε * x) := by
  have hlaw : R.map (fun ξ => (S ξ, T ξ)) = P.prod (LatticeProb.uniformIco ε) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hS.aemeasurable hT.aemeasurable).1 hind,
      hS_law, hT_law]
  have hp : Measure.QuasiMeasurePreserving (fun ξ => (S ξ, T ξ)) R
      (P.prod (LatticeProb.uniformIco ε)) := by
    refine ⟨hS.prodMk hT, ?_⟩
    rw [hlaw]
  exact hp.ae (ae_prod_shifted_cellularEmbedding_uniformIco D hε)

end MatedCRTHarmonic.MoTInput
end
