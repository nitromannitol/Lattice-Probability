import LatticeProb.LQG.AEFieldObservation
import LatticeProb.LQG.NestedDiscreteHull
import LatticeProb.Prob.AELeSigmaInfimum

/-! # Germs of almost-equal field observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.Blueprint

namespace LatticeProb.LQG

/-- Almost-equal fields give almost-surely contained fixed-family hull germs. -/
theorem aeLeSigma_iInf_iSup_localHullFieldSigma_of_ae_eq {Ω : Type}
    {m : MeasurableSpace Ω} {μ : Measure[m] Ω}
    {h g : Ω → DistC} (heq : h =ᵐ[μ] g) (A : Ω → Set ℂ)
    (hclosed : ∀ ω, IsClosed (A ω)) (hbounded : ∀ ω, Bornology.IsBounded (A ω))
    (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p) :
    AELeSigma (⨅ n, ⨆ k, localHullFieldSigma h A n (ψ k) hp)
      (⨅ n, ⨆ k, localHullFieldSigma g A n (ψ k) hp) μ := by
  apply AELeSigma.iInf_of_antitone (antitone_iSup_localHullFieldSigma g A hclosed hbounded ψ hp)
  intro n
  apply AELeSigma.iSup
  intro k s hs
  have hlocal : AELeSigma (localHullFieldSigma h A n (ψ k) hp)
      (localHullFieldSigma g A n (ψ k) hp) μ := by
    simpa only [bot_sup_eq] using
      (aeLeSigma_localHullFieldSigma_of_ae_eq ⊥ heq A n (ψ k) hp)
  obtain ⟨t, ht, hst⟩ := hlocal s hs
  exact ⟨t, (le_iSup (fun j => localHullFieldSigma g A n (ψ j) hp) k) _ ht, hst⟩

/-- Joining a shared history preserves the comparison of the field germs. -/
theorem aeLeSigma_joined_iInf_iSup_localHullFieldSigma_of_ae_eq {Ω : Type}
    {m : MeasurableSpace Ω} {μ : Measure[m] Ω} (H : MeasurableSpace Ω)
    {h g : Ω → DistC} (heq : h =ᵐ[μ] g) (A : Ω → Set ℂ)
    (hclosed : ∀ ω, IsClosed (A ω)) (hbounded : ∀ ω, Bornology.IsBounded (A ω))
    (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p) :
    AELeSigma (H ⊔ ⨅ n, ⨆ k, localHullFieldSigma h A n (ψ k) hp)
      (H ⊔ ⨅ n, ⨆ k, localHullFieldSigma g A n (ψ k) hp) μ := by
  apply AELeSigma.sup (AELeSigma.of_le le_sup_left)
  intro s hs
  obtain ⟨t, ht, hst⟩ :=
    aeLeSigma_iInf_iSup_localHullFieldSigma_of_ae_eq heq A hclosed hbounded ψ hp s hs
  exact ⟨t, (le_sup_right : (⨅ n, ⨆ k, localHullFieldSigma g A n (ψ k) hp) ≤
    H ⊔ (⨅ n, ⨆ k, localHullFieldSigma g A n (ψ k) hp)) _ ht, hst⟩

/-- Conditional expectations given joined fixed-family hull germs agree for
almost-equal fields when both histories are ambient measurable. -/
theorem condExp_iInf_iSup_localHullFieldSigma_ae_eq_of_ae_eq {Ω : Type}
    {m : MeasurableSpace Ω} {μ : Measure[m] Ω} [IsFiniteMeasure μ]
    (H : MeasurableSpace Ω) {h g : Ω → DistC} (heq : h =ᵐ[μ] g) (A : Ω → Set ℂ)
    (hclosed : ∀ ω, IsClosed (A ω)) (hbounded : ∀ ω, Bornology.IsBounded (A ω))
    (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p)
    (hh : H ⊔ (⨅ n, ⨆ k, localHullFieldSigma h A n (ψ k) hp) ≤ m)
    (hg : H ⊔ (⨅ n, ⨆ k, localHullFieldSigma g A n (ψ k) hp) ≤ m)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | H ⊔ ⨅ n, ⨆ k, localHullFieldSigma h A n (ψ k) hp] =ᵐ[μ]
      μ[f | H ⊔ ⨅ n, ⨆ k, localHullFieldSigma g A n (ψ k) hp] :=
  condExp_ae_eq_of_mutual_aeLeSigma hh hg
    (aeLeSigma_joined_iInf_iSup_localHullFieldSigma_of_ae_eq H heq A hclosed hbounded ψ hp)
    (aeLeSigma_joined_iInf_iSup_localHullFieldSigma_of_ae_eq H heq.symm A hclosed hbounded ψ hp) hf

end LatticeProb.LQG
