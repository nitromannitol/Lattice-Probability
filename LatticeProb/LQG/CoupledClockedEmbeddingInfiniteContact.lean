import LatticeProb.LQG.CoupledClockedEmbeddingCells
import LatticeProb.LQG.CoupledClockedInfiniteContact

/-! # Infinite contact in coupled clocked embeddings -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace LatticeProb

/-- At a fixed positive mesh, the rooted embedding and the infinite-contact
implications hold for the same clocked contour on one product-full event. -/
theorem exists_coupled_clocked_embedding_infinite_contact
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    (ε : ℝ) (hε : 0 < ε) (Q : Measure ℝ) [SFinite Q] (hQ : Q ≪ volume) :
    ∃ G : Ω → Path2, Measurable G ∧
      ∀ᵐ p ∂P.prod Q, 0 ≤ p.2 → p.2 ≤ 1 →
        let c := CellScaling.JointScalingO.clock γ
          (coneField (X p.1) (coneRadial γ γ (fun u => B u p.1) (fun u => B' u p.1)))
          (η₀ p.1)
        let w : Path2 := ⟨fun t => G p.1 (t + ε * p.2),
          (G p.1).continuous.comp (by fun_prop)⟩
        ∃ (hlf : IsLocallyFinite ε w)
          (H : CellularEmbedding (MatedCRT.graph ε w hlf) 0),
          (∀ j : ℤ, H.cell j = η p.1 '' Icc
            (c (ε * ((j : ℝ) - 1 + p.2))) (c (ε * ((j : ℝ) + p.2)))) ∧
          ∀ (b : Bool) (i j : ℤ), i + 1 < j →
            MatedCRT.SideCond ε
              (fun t => if b then (w t).2 else (w t).1) i j →
            (H.cell i ∩ H.cell j).Infinite := by
  obtain ⟨G, hG, hclock, hemb⟩ :=
    exists_coupled_clocked_embedding_area_cells hC hγ hf ε hε Q hQ
  obtain ⟨F, _, hclock', hcontact⟩ :=
    exists_coupled_clocked_infinite_contact hC hγ hf ε hε Q hQ
  have heq : ∀ᵐ ω ∂P, G ω = F ω := by
    filter_upwards [hclock, hclock'] with ω h₁ h₂
    obtain ⟨ψ₁, _, _, hGψ, hc₁, _⟩ := h₁
    obtain ⟨ψ₂, _, _, hFψ, hc₂, _⟩ := h₂
    apply ContinuousMap.ext
    intro t
    rw [hGψ t, hFψ t, ← hc₁ t, ← hc₂ t]
  have heqprod :=
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).tendsto_ae.eventually heq
  refine ⟨G, hG, ?_⟩
  filter_upwards [hemb, hcontact, heqprod] with p hemb hcontact heq
  intro hθ0 hθ1
  obtain ⟨hlf, H, hH⟩ := hemb.1 hθ0 hθ1
  refine ⟨hlf, H, hH, ?_⟩
  intro b i j hij hside
  rw [hH i, hH j]
  apply hcontact b i j hij
  simpa only [← heq, ContinuousMap.coe_mk] using hside

end LatticeProb
