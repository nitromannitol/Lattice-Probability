import LatticeProb.LQG.CollarCarrierCofinal
import LatticeProb.Prob.FullCarrierHistory

/-! # Conditional expectations for cofinal collar germs -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric

namespace LatticeProb.LQG

/-- On a full compact-anchor carrier, cofinal collar germs yield the same
conditional expectation, provided both histories are ambient measurable. -/
theorem condExp_collar_germ_ae_eq_of_cofinal {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    {m : MeasurableSpace Ω} {μ : Measure[m] Ω} [IsFiniteMeasure μ]
    (H : MeasurableSpace Ω) (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (z : ℂ) (ψ : ℕ → TestC) (hψ : ∀ n, ∫ x, ψ n x = 1)
    (hsupp : ∀ n ω, z ∈ (K ω : Set ℂ) → tsupport (ψ n : ℂ → ℝ) ⊆
      thickening (1 / ((n : ℝ) + 1)) (K ω : Set ℂ))
    {p : ℝ} (hp : 0 < p) (q : ℕ → ℕ) (hq : ∀ n, ∃ j, n ≤ q j)
    (hA : ∀ᵐ ω ∂μ, z ∈ (K ω : Set ℂ))
    (hall : H ⊔ (⨅ n, MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp n) inferInstance) ≤ m)
    (hcofinal : H ⊔ (⨅ j, MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp (q j)) inferInstance) ≤ m)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | H ⊔ ⨅ n, MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp n) inferInstance] =ᵐ[μ]
    μ[f | H ⊔ ⨅ j, MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp (q j)) inferInstance] :=
  LatticeProb.condExp_ae_eq_of_comap_subtype_eq hA hall hcofinal
    (comap_anchorCarrier_collar_germ_eq_of_cofinal H h K z ψ hψ hsupp hp q hq) hf

/-- Dyadic reciprocal collars yield the same conditional expectation as all
reciprocal collars on a full compact-anchor carrier. -/
theorem condExp_collar_germ_ae_eq_dyadic {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    {m : MeasurableSpace Ω} {μ : Measure[m] Ω} [IsFiniteMeasure μ]
    (H : MeasurableSpace Ω) (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (z : ℂ) (ψ : ℕ → TestC) (hψ : ∀ n, ∫ x, ψ n x = 1)
    (hsupp : ∀ n ω, z ∈ (K ω : Set ℂ) → tsupport (ψ n : ℂ → ℝ) ⊆
      thickening (1 / ((n : ℝ) + 1)) (K ω : Set ℂ))
    {p : ℝ} (hp : 0 < p) (hA : ∀ᵐ ω ∂μ, z ∈ (K ω : Set ℂ))
    (hall : H ⊔ (⨅ n, MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp n) inferInstance) ≤ m)
    (hdyadic : H ⊔ (⨅ j, MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp (2 ^ j - 1)) inferInstance) ≤ m)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | H ⊔ ⨅ n, MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp n) inferInstance] =ᵐ[μ]
    μ[f | H ⊔ ⨅ j, MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp (2 ^ j - 1)) inferInstance] :=
  LatticeProb.condExp_ae_eq_of_comap_subtype_eq hA hall hdyadic
    (comap_anchorCarrier_collar_germ_eq_dyadic H h K z ψ hψ hsupp hp) hf

end LatticeProb.LQG
