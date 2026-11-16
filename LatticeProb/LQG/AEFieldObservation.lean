import LatticeProb.LQG.AnchorCarrierHistory

/-! # Fixed-scale observations of almost-equal random fields -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set TopologicalSpace LQGMetric LQGMetric.Blueprint

namespace LatticeProb.LQG

/-- Almost-equal fields give equal hull observations up to null sets, even after
joining a common history. -/
theorem aeLeSigma_localHullFieldSigma_of_ae_eq {Ω : Type}
    {m : MeasurableSpace Ω} {μ : Measure[m] Ω} (H : MeasurableSpace Ω)
    {h g : Ω → DistC} (heq : h =ᵐ[μ] g) (A : Ω → Set ℂ)
    (n : ℕ) (a : TestC) {p : ℝ} (hp : 0 < p) :
    AELeSigma (H ⊔ localHullFieldSigma h A n a hp)
      (H ⊔ localHullFieldSigma g A n a hp) μ := by
  let S : Set Ω := {ω | h ω = g ω}
  apply AELeSigma.of_comap_subtype_le (A := S) heq
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_sup,
    comap_localHullFieldSigma, comap_localHullFieldSigma]
  have hS : h ∘ (Subtype.val : S → Ω) = g ∘ (Subtype.val : S → Ω) := by
    funext ω
    exact ω.property
  rw [hS]

/-- Almost-equal fields give equal collar-code observations up to null sets,
even after joining a common history. -/
theorem aeLeSigma_collarFieldCode_of_ae_eq {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)]
    {m : MeasurableSpace Ω} {μ : Measure[m] Ω} (H : MeasurableSpace Ω)
    {h g : Ω → DistC} (heq : h =ᵐ[μ] g) (K : Ω → NonemptyCompacts ℂ)
    {I : Type*} (φ : I → TestC) (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p) (k : ℕ) :
    AELeSigma (H ⊔ MeasurableSpace.comap (collarFieldCode h K φ ψ hp k) inferInstance)
      (H ⊔ MeasurableSpace.comap (collarFieldCode g K φ ψ hp k) inferInstance) μ := by
  let S : Set Ω := {ω | h ω = g ω}
  apply AELeSigma.of_comap_subtype_le (A := S) heq
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_sup,
    comap_collarFieldCode, comap_collarFieldCode]
  have hS : h ∘ (Subtype.val : S → Ω) = g ∘ (Subtype.val : S → Ω) := by
    funext ω
    exact ω.property
  rw [hS]

/-- Conditional expectations given joined hull observations agree for
almost-equal fields when both histories are ambient measurable. -/
theorem condExp_localHullFieldSigma_ae_eq_of_ae_eq {Ω : Type}
    {m : MeasurableSpace Ω} {μ : Measure[m] Ω} [IsFiniteMeasure μ]
    (H : MeasurableSpace Ω) {h g : Ω → DistC} (heq : h =ᵐ[μ] g)
    (A : Ω → Set ℂ) (n : ℕ) (a : TestC) {p : ℝ} (hp : 0 < p)
    (hh : H ⊔ localHullFieldSigma h A n a hp ≤ m)
    (hg : H ⊔ localHullFieldSigma g A n a hp ≤ m)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | H ⊔ localHullFieldSigma h A n a hp] =ᵐ[μ]
      μ[f | H ⊔ localHullFieldSigma g A n a hp] :=
  condExp_ae_eq_of_mutual_aeLeSigma hh hg
    (aeLeSigma_localHullFieldSigma_of_ae_eq H heq A n a hp)
    (aeLeSigma_localHullFieldSigma_of_ae_eq H heq.symm A n a hp) hf

/-- Conditional expectations given joined collar observations agree for
almost-equal fields when both histories are ambient measurable. -/
theorem condExp_collarFieldCode_ae_eq_of_ae_eq {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)]
    {m : MeasurableSpace Ω} {μ : Measure[m] Ω} [IsFiniteMeasure μ]
    (H : MeasurableSpace Ω) {h g : Ω → DistC} (heq : h =ᵐ[μ] g)
    (K : Ω → NonemptyCompacts ℂ) {I : Type*} (φ : I → TestC)
    (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p) (k : ℕ)
    (hh : H ⊔ MeasurableSpace.comap (collarFieldCode h K φ ψ hp k) inferInstance ≤ m)
    (hg : H ⊔ MeasurableSpace.comap (collarFieldCode g K φ ψ hp k) inferInstance ≤ m)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | H ⊔ MeasurableSpace.comap (collarFieldCode h K φ ψ hp k) inferInstance] =ᵐ[μ]
      μ[f | H ⊔ MeasurableSpace.comap (collarFieldCode g K φ ψ hp k) inferInstance] :=
  condExp_ae_eq_of_mutual_aeLeSigma hh hg
    (aeLeSigma_collarFieldCode_of_ae_eq H heq K φ ψ hp k)
    (aeLeSigma_collarFieldCode_of_ae_eq H heq.symm K φ ψ hp k) hf

end LatticeProb.LQG
