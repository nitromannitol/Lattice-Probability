import LatticeProb.Prob.CondExpComapMap

/-! # Conditional event bounds under a measurable realization -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- A conditional lower bound on a law passes to any measurable realization,
when conditioning on the pullback of the original observation. -/
theorem condExp_indicator_const_le_of_map_eq
    {Ω E : Type*} [m : MeasurableSpace Ω] [mE : MeasurableSpace E]
    {G : MeasurableSpace E}
    (μ : Measure Ω) [IsFiniteMeasure μ] (ν : @Measure E mE)
    (π : Ω → E) (hπ : @Measurable Ω E m mE π) (hlaw : @Measure.map Ω E m mE π μ = ν)
    (hG : G ≤ mE) (A : Set E) (hA : @MeasurableSet E mE A) {p : ℝ}
    (hp : ∀ᵐ x ∂ν, p ≤ ν[A.indicator (fun _ => (1 : ℝ)) | G] x) :
    ∀ᵐ ω ∂μ, p ≤ μ[(π ⁻¹' A).indicator (fun _ => (1 : ℝ)) | G.comap π] ω := by
  let _ : MeasurableSpace E := mE
  have hF : @Measurable E ℝ mE _ (A.indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator hA
  have hbound : ∀ x, |A.indicator (fun _ => (1 : ℝ)) x| ≤ (1 : ℝ) := by
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  have hcond := condExp_comp_comap_ae_eq (μ := μ) (G := G) (m' := mE) hπ hG hF hbound
  rw [hlaw] at hcond
  have hmeas : @MeasurableSet E mE {x | p ≤ ν[A.indicator (fun _ => (1 : ℝ)) | G] x} :=
    measurableSet_le measurable_const
      (stronglyMeasurable_condExp.measurable.mono hG le_rfl)
  have hpull : ∀ᵐ ω ∂μ, p ≤ ν[A.indicator (fun _ => (1 : ℝ)) | G] (π ω) := by
    apply (ae_map_iff hπ.aemeasurable hmeas).1
    simpa only [hlaw] using hp
  filter_upwards [hcond, hpull] with ω heq hω
  have hind : (fun ω => A.indicator (fun _ => (1 : ℝ)) (π ω)) =
      (π ⁻¹' A).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h : π ω ∈ A <;> simp [h]
  rw [hind] at heq
  exact heq.symm ▸ hω

end LatticeProb
