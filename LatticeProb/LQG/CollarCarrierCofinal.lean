import LatticeProb.LQG.CollarCofinalGerm
import LatticeProb.LQG.CompactAnchorCarrier
import LatticeProb.LQG.HullObservationPullback

/-! # Cofinal collar germs on a compact-anchor carrier -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric

namespace LatticeProb.LQG

/-- A cofinal family determines the same joined collar germ after restriction
 to the carrier on which the anchor support condition holds. -/
theorem comap_anchorCarrier_collar_germ_eq_of_cofinal {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (H : MeasurableSpace Ω) (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (z : ℂ) (ψ : ℕ → TestC) (hψ : ∀ n, ∫ x, ψ n x = 1)
    (hsupp : ∀ n ω, z ∈ (K ω : Set ℂ) → tsupport (ψ n : ℂ → ℝ) ⊆
      thickening (1 / ((n : ℝ) + 1)) (K ω : Set ℂ))
    {p : ℝ} (hp : 0 < p) (f : ℕ → ℕ) (hf : ∀ n, ∃ j, n ≤ f j) :
    let A := {ω | z ∈ (K ω : Set ℂ)}
    MeasurableSpace.comap (Subtype.val : A → Ω)
      (H ⊔ ⨅ n, MeasurableSpace.comap
        (collarFieldCode h K localDenseTest ψ hp n) inferInstance) =
    MeasurableSpace.comap (Subtype.val : A → Ω)
      (H ⊔ ⨅ j, MeasurableSpace.comap
        (collarFieldCode h K localDenseTest ψ hp (f j)) inferInstance) := by
  dsimp only
  rw [comap_anchorCarrier_collar_germ H h K z ψ hp]
  rw [LatticeProb.comap_subtype_sup_iInf_of_measurable H _ _
    (fun j => measurableSet_mem_compact_of_collarFieldCode h K z ψ hp (f j))]
  congr 1
  simp_rw [comap_collarFieldCode]
  have hs : ∀ n (ω : {ω | z ∈ (K ω : Set ℂ)}),
      tsupport (ψ n : ℂ → ℝ) ⊆
        thickening (1 / ((n : ℝ) + 1)) ((K ∘ Subtype.val) ω : Set ℂ) := by
    intro n ω
    exact hsupp n ω.val ω.property
  simpa only [bot_sup_eq] using
    (iInf_sup_collarFieldCode_eq_of_cofinal (h ∘ Subtype.val) (K ∘ Subtype.val)
      ψ hψ hs hp ⊥ f hf)

/-- Dyadic reciprocal scales determine the restricted joined collar germ. -/
theorem comap_anchorCarrier_collar_germ_eq_dyadic {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (H : MeasurableSpace Ω) (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (z : ℂ) (ψ : ℕ → TestC) (hψ : ∀ n, ∫ x, ψ n x = 1)
    (hsupp : ∀ n ω, z ∈ (K ω : Set ℂ) → tsupport (ψ n : ℂ → ℝ) ⊆
      thickening (1 / ((n : ℝ) + 1)) (K ω : Set ℂ))
    {p : ℝ} (hp : 0 < p) :
    let A := {ω | z ∈ (K ω : Set ℂ)}
    MeasurableSpace.comap (Subtype.val : A → Ω)
      (H ⊔ ⨅ n, MeasurableSpace.comap
        (collarFieldCode h K localDenseTest ψ hp n) inferInstance) =
    MeasurableSpace.comap (Subtype.val : A → Ω)
      (H ⊔ ⨅ j, MeasurableSpace.comap
        (collarFieldCode h K localDenseTest ψ hp (2 ^ j - 1)) inferInstance) := by
  apply comap_anchorCarrier_collar_germ_eq_of_cofinal H h K z ψ hψ hsupp hp
  intro n
  exact ⟨n, Nat.le_sub_one_of_lt n.lt_two_pow_self⟩

end LatticeProb.LQG
