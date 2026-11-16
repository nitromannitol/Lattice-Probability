import LatticeProb.LQG.AnchorCarrierHistory
import LatticeProb.LQG.CollarAnchorChange

/-! # Anchor changes for collar histories on a compact carrier -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric

namespace LatticeProb.LQG

/-- Supported unit-integral anchors determine the same joined collar germ on
 the carrier where the observed compact contains the fixed point. -/
theorem comap_anchorCarrier_collar_history_eq_of_anchors_supported {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (H : MeasurableSpace Ω) (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (z : ℂ) (ψ χ : ℕ → TestC) (hψ : ∀ k, ∫ x, ψ k x = 1)
    (hχ : ∀ k, ∫ x, χ k x = 1)
    (hsψ : ∀ k ω, z ∈ (K ω : Set ℂ) → tsupport (ψ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    (hsχ : ∀ k ω, z ∈ (K ω : Set ℂ) → tsupport (χ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    {p : ℝ} (hp : 0 < p) :
    let A := {ω | z ∈ (K ω : Set ℂ)}
    MeasurableSpace.comap (Subtype.val : A → Ω)
      (H ⊔ ⨅ k, MeasurableSpace.comap
        (collarFieldCode h K localDenseTest ψ hp k) inferInstance) =
    MeasurableSpace.comap (Subtype.val : A → Ω)
      (H ⊔ ⨅ k, MeasurableSpace.comap
        (collarFieldCode h K localDenseTest χ hp k) inferInstance) := by
  dsimp only
  rw [comap_anchorCarrier_collar_germ H h K z ψ hp,
    comap_anchorCarrier_collar_germ H h K z χ hp]
  congr 1
  apply iInf_congr
  intro k
  simp_rw [comap_collarFieldCode]
  apply comap_collarFieldCode_eq_of_anchors_supported _ _ ψ χ hp k (hψ k) (hχ k)
  · intro ω
    exact hsψ k ω.val ω.property
  · intro ω
    exact hsχ k ω.val ω.property

/-- On a full-measure carrier, the joined collar germs have identical
conditional expectations under either supported unit-integral anchor family. -/
theorem condExp_collar_history_ae_eq_of_anchors_supported {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    {m : MeasurableSpace Ω} {μ : Measure[m] Ω} [IsFiniteMeasure μ]
    (H : MeasurableSpace Ω) (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (z : ℂ) (ψ χ : ℕ → TestC) (hψ : ∀ k, ∫ x, ψ k x = 1)
    (hχ : ∀ k, ∫ x, χ k x = 1)
    (hsψ : ∀ k ω, z ∈ (K ω : Set ℂ) → tsupport (ψ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    (hsχ : ∀ k ω, z ∈ (K ω : Set ℂ) → tsupport (χ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    {p : ℝ} (hp : 0 < p) (hA : ∀ᵐ ω ∂μ, z ∈ (K ω : Set ℂ))
    (hψm : H ⊔ (⨅ k, MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp k) inferInstance) ≤ m)
    (hχm : H ⊔ (⨅ k, MeasurableSpace.comap
      (collarFieldCode h K localDenseTest χ hp k) inferInstance) ≤ m)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | H ⊔ ⨅ k, MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp k) inferInstance] =ᵐ[μ]
    μ[f | H ⊔ ⨅ k, MeasurableSpace.comap
      (collarFieldCode h K localDenseTest χ hp k) inferInstance] :=
  LatticeProb.condExp_ae_eq_of_comap_subtype_eq hA hψm hχm
    (comap_anchorCarrier_collar_history_eq_of_anchors_supported H h K z ψ χ
      hψ hχ hsψ hsχ hp) hf

end LatticeProb.LQG
