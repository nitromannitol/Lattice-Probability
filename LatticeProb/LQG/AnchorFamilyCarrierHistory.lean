import LatticeProb.LQG.CompactAnchorCarrier
import LatticeProb.LQG.HullObservationPullback
import LatticeProb.LQG.HullAnchorFamilyReduction
import LatticeProb.Prob.FullCarrierHistory

/-! # Anchor family observation histories on a compact carrier -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set TopologicalSpace LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- On the compact-anchor carrier a family germ has the same trace as the
selected supported-anchor germ, even after adjoining a common history. -/
theorem comap_anchorCarrier_family_hull_history_eq {Ω : Type} {I : Type*}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (H : MeasurableSpace Ω) (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (z : ℂ) (ψ : I → TestC) (i : ℕ → I) (hψ : ∀ j, ∫ x, ψ j x = 1)
    (hsupp : ∀ n ω, z ∈ (K ω : Set ℂ) →
      tsupport (ψ (i n) : ℂ → ℝ) ⊆ interior (dyadicHull n (K ω : Set ℂ)))
    {p : ℝ} (hp : 0 < p) :
    let A := {ω | z ∈ (K ω : Set ℂ)}
    MeasurableSpace.comap (Subtype.val : A → Ω)
      (H ⊔ ⨅ n, ⨆ j, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (ψ j) hp) =
    MeasurableSpace.comap (Subtype.val : A → Ω)
      (H ⊔ ⨅ n, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (ψ (i n)) hp) := by
  dsimp only
  rw [LatticeProb.comap_subtype_sup_iInf_of_measurable]
  · rw [comap_anchorCarrier_hull_germ]
    congr 1
    simp_rw [MeasurableSpace.comap_iSup, comap_localHullFieldSigma]
    apply iInf_iSup_localHullFieldSigma_eq (h ∘ Subtype.val)
      ((fun ω => (K ω : Set ℂ)) ∘ Subtype.val)
      (fun ω => (K ω.val).isCompact.isBounded) ψ i hψ
    intro n ω
    exact hsupp n ω.val ω.property
  · intro n
    exact (le_iSup (fun j => localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (ψ j) hp)
      (i n)) _ (measurableSet_mem_compact_of_localHullFieldSigma h K z n (ψ (i n)) hp)

/-- On a full-measure carrier, the family and selected-anchor histories give
identical conditional expectations for integrable tests. -/
theorem condExp_family_hull_history_ae_eq_selected {Ω : Type} {I : Type*}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    {m : MeasurableSpace Ω} {μ : Measure[m] Ω} [IsFiniteMeasure μ]
    (H : MeasurableSpace Ω) (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (z : ℂ) (ψ : I → TestC) (i : ℕ → I) (hψ : ∀ j, ∫ x, ψ j x = 1)
    (hsupp : ∀ n ω, z ∈ (K ω : Set ℂ) →
      tsupport (ψ (i n) : ℂ → ℝ) ⊆ interior (dyadicHull n (K ω : Set ℂ)))
    {p : ℝ} (hp : 0 < p) (hA : ∀ᵐ ω ∂μ, z ∈ (K ω : Set ℂ))
    (hfamily : H ⊔ (⨅ n, ⨆ j, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (ψ j) hp) ≤ m)
    (hselected : H ⊔ (⨅ n, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (ψ (i n)) hp) ≤ m)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | H ⊔ ⨅ n, ⨆ j, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (ψ j) hp] =ᵐ[μ]
      μ[f | H ⊔ ⨅ n, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (ψ (i n)) hp] :=
  LatticeProb.condExp_ae_eq_of_comap_subtype_eq hA hfamily hselected
    (comap_anchorCarrier_family_hull_history_eq H h K z ψ i hψ hsupp hp) hf

end LatticeProb.LQG
