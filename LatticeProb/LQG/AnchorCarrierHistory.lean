import LatticeProb.LQG.CompactAnchorCarrier
import LatticeProb.LQG.HullObservationPullback
import LatticeProb.Prob.FullCarrierHistory

/-! # Observation histories on a compact-anchor carrier -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

set_option maxHeartbeats 400000 in
/-- The joined hull and collar histories have equal traces on the event that
all observed compacts contain the fixed anchor. -/
theorem comap_anchorCarrier_hull_history_eq_collar_history {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (H : MeasurableSpace Ω) (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (z : ℂ) (a ψ : ℕ → TestC) (ha : ∀ n, ∫ x, a n x = 1)
    (hasupp : ∀ n ω, z ∈ (K ω : Set ℂ) → tsupport (a n : ℂ → ℝ) ⊆
      interior (dyadicHull n (K ω : Set ℂ)))
    (hψ : ∀ k, ∫ x, ψ k x = 1)
    (hψsupp : ∀ k ω, z ∈ (K ω : Set ℂ) → tsupport (ψ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    {p : ℝ} (hp : 0 < p) :
    let A := {ω | z ∈ (K ω : Set ℂ)}
    MeasurableSpace.comap (Subtype.val : A → Ω)
        (H ⊔ ⨅ n, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (a n) hp) =
      MeasurableSpace.comap (Subtype.val : A → Ω)
        (H ⊔ ⨅ k, MeasurableSpace.comap
          (collarFieldCode h K localDenseTest ψ hp k) inferInstance) := by
  dsimp only
  rw [comap_anchorCarrier_hull_germ, comap_anchorCarrier_collar_germ]
  congr 1
  simp_rw [comap_localHullFieldSigma, comap_collarFieldCode]
  apply iInf_localHullFieldSigma_eq_iInf_collarFieldCode
    (h ∘ Subtype.val) (K ∘ Subtype.val) z (fun ω => ω.property) a ψ ha
  · intro n ω
    exact hasupp n ω.val ω.property
  · exact hψ
  · intro k ω
    exact hψsupp k ω.val ω.property

/-- Equal traces on a full-measure anchor carrier give equal conditional
expectations for the corresponding joined histories. -/
theorem condExp_hull_history_ae_eq_collar_history {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    {m : MeasurableSpace Ω} {μ : Measure[m] Ω} [IsFiniteMeasure μ]
    (H : MeasurableSpace Ω) (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (z : ℂ) (a ψ : ℕ → TestC) (ha : ∀ n, ∫ x, a n x = 1)
    (hasupp : ∀ n ω, z ∈ (K ω : Set ℂ) → tsupport (a n : ℂ → ℝ) ⊆
      interior (dyadicHull n (K ω : Set ℂ)))
    (hψ : ∀ k, ∫ x, ψ k x = 1)
    (hψsupp : ∀ k ω, z ∈ (K ω : Set ℂ) → tsupport (ψ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    {p : ℝ} (hp : 0 < p) (hA : ∀ᵐ ω ∂μ, z ∈ (K ω : Set ℂ))
    (hHull : H ⊔ (⨅ n, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (a n) hp) ≤ m)
    (hCollar : H ⊔ (⨅ k, MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp k) inferInstance) ≤ m)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | H ⊔ ⨅ n, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (a n) hp] =ᵐ[μ]
      μ[f | H ⊔ ⨅ k, MeasurableSpace.comap
        (collarFieldCode h K localDenseTest ψ hp k) inferInstance] :=
  LatticeProb.condExp_ae_eq_of_comap_subtype_eq hA hHull hCollar
    (comap_anchorCarrier_hull_history_eq_collar_history H h K z a ψ ha hasupp hψ hψsupp hp) hf

end LatticeProb.LQG
