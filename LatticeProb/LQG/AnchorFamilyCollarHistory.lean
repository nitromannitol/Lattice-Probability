import LatticeProb.LQG.AnchorFamilyCarrierHistory
import LatticeProb.LQG.AnchorCarrierHistory

/-! # Family hull and collar observation histories on a compact carrier -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- A family hull history and a collar history have equal traces on the event
that the observed compact contains the fixed anchor. -/
theorem comap_anchorCarrier_family_hull_history_eq_collar_history {Ω : Type} {I : Type*}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (H : MeasurableSpace Ω) (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (z : ℂ) (α : I → TestC) (i : ℕ → I) (hα : ∀ j, ∫ x, α j x = 1)
    (hαsupp : ∀ n ω, z ∈ (K ω : Set ℂ) →
      tsupport (α (i n) : ℂ → ℝ) ⊆ interior (dyadicHull n (K ω : Set ℂ)))
    (ψ : ℕ → TestC) (hψ : ∀ k, ∫ x, ψ k x = 1)
    (hψsupp : ∀ k ω, z ∈ (K ω : Set ℂ) → tsupport (ψ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    {p : ℝ} (hp : 0 < p) :
    let A := {ω | z ∈ (K ω : Set ℂ)}
    MeasurableSpace.comap (Subtype.val : A → Ω)
        (H ⊔ ⨅ n, ⨆ j, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (α j) hp) =
      MeasurableSpace.comap (Subtype.val : A → Ω)
        (H ⊔ ⨅ k, MeasurableSpace.comap
          (collarFieldCode h K localDenseTest ψ hp k) inferInstance) :=
  (comap_anchorCarrier_family_hull_history_eq H h K z α i hα hαsupp hp).trans
    (comap_anchorCarrier_hull_history_eq_collar_history H h K z (fun n => α (i n)) ψ
      (fun n => hα (i n)) hαsupp hψ hψsupp hp)

/-- On a full-measure anchor carrier, the family hull and collar histories give
identical conditional expectations for integrable tests. -/
theorem condExp_family_hull_history_ae_eq_collar_history {Ω : Type} {I : Type*}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    {m : MeasurableSpace Ω} {μ : Measure[m] Ω} [IsFiniteMeasure μ]
    (H : MeasurableSpace Ω) (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (z : ℂ) (α : I → TestC) (i : ℕ → I) (hα : ∀ j, ∫ x, α j x = 1)
    (hαsupp : ∀ n ω, z ∈ (K ω : Set ℂ) →
      tsupport (α (i n) : ℂ → ℝ) ⊆ interior (dyadicHull n (K ω : Set ℂ)))
    (ψ : ℕ → TestC) (hψ : ∀ k, ∫ x, ψ k x = 1)
    (hψsupp : ∀ k ω, z ∈ (K ω : Set ℂ) → tsupport (ψ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    {p : ℝ} (hp : 0 < p) (hA : ∀ᵐ ω ∂μ, z ∈ (K ω : Set ℂ))
    (hfamily : H ⊔ (⨅ n, ⨆ j, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (α j) hp) ≤ m)
    (hcollar : H ⊔ (⨅ k, MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp k) inferInstance) ≤ m)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | H ⊔ ⨅ n, ⨆ j, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (α j) hp] =ᵐ[μ]
      μ[f | H ⊔ ⨅ k, MeasurableSpace.comap
        (collarFieldCode h K localDenseTest ψ hp k) inferInstance] :=
  LatticeProb.condExp_ae_eq_of_comap_subtype_eq hA hfamily hcollar
    (comap_anchorCarrier_family_hull_history_eq_collar_history H h K z α i hα hαsupp
      ψ hψ hψsupp hp) hf

end LatticeProb.LQG
