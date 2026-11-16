import LatticeProb.LQG.NestedCollarCode

/-! # Cofinal families of collar observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric

namespace LatticeProb.LQG

/-- Reciprocal collar observation σ-algebras decrease with the collar radius. -/
theorem antitone_collarFieldCode_sigma {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    (hψ : ∀ n, ∫ z, ψ n z = 1)
    (hsupp : ∀ n ω, tsupport (ψ n : ℂ → ℝ) ⊆
      thickening (1 / ((n : ℝ) + 1)) (K ω : Set ℂ))
    {p : ℝ} (hp : 0 < p) :
    Antitone (fun n => MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp n) inferInstance) := by
  intro k n hkn
  apply comap_collarFieldCode_le_of_le h K localDenseTest ψ hp hkn (hψ n)
  intro ω
  apply (hsupp n ω).trans
  apply thickening_mono
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast Nat.add_le_add_right hkn 1

/-- A cofinal family of reciprocal collars determines the same germ, even
when a fixed additional σ-algebra is joined at each scale. -/
theorem iInf_sup_collarFieldCode_eq_of_cofinal {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    (hψ : ∀ n, ∫ z, ψ n z = 1)
    (hsupp : ∀ n ω, tsupport (ψ n : ℂ → ℝ) ⊆
      thickening (1 / ((n : ℝ) + 1)) (K ω : Set ℂ))
    {p : ℝ} (hp : 0 < p) (H : MeasurableSpace Ω) (f : ℕ → ℕ)
    (hf : ∀ n, ∃ j, n ≤ f j) :
    (⨅ n, H ⊔ MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp n) inferInstance) =
    (⨅ j, H ⊔ MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp (f j)) inferInstance) := by
  have ha := antitone_collarFieldCode_sigma h K ψ hψ hsupp hp
  apply le_antisymm
  · exact le_iInf fun j => iInf_le _ (f j)
  · refine le_iInf fun n => ?_
    obtain ⟨j, hj⟩ := hf n
    exact (iInf_le _ j).trans (sup_le_sup le_rfl (ha hj))

/-- Dyadic reciprocal scales determine the same joined collar germ. -/
theorem iInf_sup_collarFieldCode_eq_dyadic {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    (hψ : ∀ n, ∫ z, ψ n z = 1)
    (hsupp : ∀ n ω, tsupport (ψ n : ℂ → ℝ) ⊆
      thickening (1 / ((n : ℝ) + 1)) (K ω : Set ℂ))
    {p : ℝ} (hp : 0 < p) (H : MeasurableSpace Ω) :
    (⨅ n, H ⊔ MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp n) inferInstance) =
    (⨅ j, H ⊔ MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp (2 ^ j - 1)) inferInstance) := by
  apply iInf_sup_collarFieldCode_eq_of_cofinal h K ψ hψ hsupp hp H
  intro n
  exact ⟨n, Nat.le_sub_one_of_lt n.lt_two_pow_self⟩

end LatticeProb.LQG
