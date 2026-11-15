import LatticeProb.LQG.CouplingIndependentPhaseEmbedding

/-! # Simultaneous shifted embeddings under phase laws -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter ProbabilityTheory
open scoped NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT

/-- Countably many product-law phases yield simultaneous shifted embeddings. -/
theorem ae_countable_shifted_cellularEmbedding_of_product_law
    {γ : ℝ} {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {R : Measure Ξ}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ι : Type} [Countable ι] (ε : ι → ℝ) (hε : ∀ i, 0 < ε i)
    (Q : ι → Measure ℝ) (hQfinite : ∀ i, SFinite (Q i))
    (hQ : ∀ i, Q i ≪ volume)
    (hsupport : ∀ i, ∀ᵐ c ∂Q i, c ∈ Icc (0 : ℝ) (ε i))
    (S : Ξ → Ω) (T : ι → Ξ → ℝ) (hS : Measurable S)
    (hT : ∀ i, Measurable (T i))
    (hlaw : ∀ i, R.map (fun ξ => (S ξ, T i ξ)) = P.prod (Q i)) :
    ∀ᵐ ξ ∂(R), ∀ i,
      let w : Path2 := ⟨fun t => bm (S ξ) (t + T i ξ),
        (bm (S ξ)).continuous.comp (by fun_prop)⟩
      ∃ (hlf : IsLocallyFinite (ε i) w)
        (H : CellularEmbedding (MatedCRT.graph (ε i) w hlf) 0),
        H.cell = fun x : ℤ => (fun t => η (S ξ) (t + T i ξ)) ''
          Icc (ε i * ((x : ℝ) - 1)) (ε i * x) := by
  refine ae_all_iff.2 fun i => ?_
  let : SFinite (Q i) := hQfinite i
  exact ae_shifted_cellularEmbedding_of_product_law D (hε i) (Q i) (hQ i)
    (hsupport i) S (T i) hS (hT i) (hlaw i)

/-- Countably many individually independent uniform phases yield simultaneous
shifted embeddings; no independence between distinct phases is required. -/
theorem ae_countable_shifted_cellularEmbedding_of_independent_uniform
    {γ : ℝ} {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {R : Measure Ξ} [IsProbabilityMeasure R]
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ι : Type} [Countable ι] (ε : ι → ℝ) (hε : ∀ i, 0 < ε i)
    (S : Ξ → Ω) (T : ι → Ξ → ℝ) (hS : Measurable S)
    (hT : ∀ i, Measurable (T i)) (hS_law : R.map S = P)
    (hT_law : ∀ i, R.map (T i) = LatticeProb.uniformIco (ε i))
    (hind : ∀ i, IndepFun S (T i) R) :
    ∀ᵐ ξ ∂(R), ∀ i,
      let w : Path2 := ⟨fun t => bm (S ξ) (t + T i ξ),
        (bm (S ξ)).continuous.comp (by fun_prop)⟩
      ∃ (hlf : IsLocallyFinite (ε i) w)
        (H : CellularEmbedding (MatedCRT.graph (ε i) w hlf) 0),
        H.cell = fun x : ℤ => (fun t => η (S ξ) (t + T i ξ)) ''
          Icc (ε i * ((x : ℝ) - 1)) (ε i * x) := by
  refine ae_all_iff.2 fun i => ?_
  exact ae_shifted_cellularEmbedding_of_independent_uniform D (hε i) S (T i)
    hS (hT i) hS_law (hT_law i) (hind i)

end MatedCRTHarmonic.MoTInput
end
