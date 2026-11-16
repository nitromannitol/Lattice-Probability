import LatticeProb.Prob.ExitObservationCondExp

/-! # Histories restricted to a full-measure carrier -/

set_option autoImplicit false

open MeasureTheory Filter Set

namespace LatticeProb

/-- Inclusion of the traces of two sigma algebras on a full-measure set gives
ambient inclusion up to null sets. The set need not belong to either history. -/
theorem AELeSigma.of_comap_subtype_le {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure[m] Ω} {F G : MeasurableSpace Ω} {A : Set Ω}
    (hA : ∀ᵐ ω ∂μ, ω ∈ A)
    (hFG : MeasurableSpace.comap (Subtype.val : A → Ω) F ≤
      MeasurableSpace.comap (Subtype.val : A → Ω) G) :
    AELeSigma F G μ := by
  intro s hs
  have htrace : MeasurableSet[MeasurableSpace.comap (Subtype.val : A → Ω) G]
      ((Subtype.val : A → Ω) ⁻¹' s) :=
    hFG _ ⟨s, hs, rfl⟩
  obtain ⟨t, ht, hst⟩ := htrace
  refine ⟨t, ht, ?_⟩
  filter_upwards [hA] with ω hω
  have hx := Set.ext_iff.mp hst ⟨ω, hω⟩
  exact propext hx.symm

/-- Equal full-carrier traces give equal conditional expectations on the ambient
space, for integrable functions and finite measures. -/
theorem condExp_ae_eq_of_comap_subtype_eq {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure[m] Ω} [IsFiniteMeasure μ] {F G : MeasurableSpace Ω}
    {A : Set Ω} (hA : ∀ᵐ ω ∂μ, ω ∈ A) (hF : F ≤ m) (hG : G ≤ m)
    (hFG : MeasurableSpace.comap (Subtype.val : A → Ω) F =
      MeasurableSpace.comap (Subtype.val : A → Ω) G)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | F] =ᵐ[μ] μ[f | G] :=
  condExp_ae_eq_of_mutual_aeLeSigma hF hG
    (AELeSigma.of_comap_subtype_le hA hFG.le)
    (AELeSigma.of_comap_subtype_le hA hFG.ge) hf

end LatticeProb
