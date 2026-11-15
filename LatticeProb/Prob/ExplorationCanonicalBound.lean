import LatticeProb.Prob.ConditionalTrialHistory
import LatticeProb.Prob.ExplorationCond

/-! # Conditional bounds on a pushforward law -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- A lower bound given a history containing the pullback of an observation
passes to the conditional expectation on the law of the observed random element. -/
theorem condExp_const_le_map_of_larger_history
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    (P : @Measure Ω mΩ) [IsProbabilityMeasure P] (Φ : Ω → E)
    (hΦ : @Measurable Ω E mΩ mE Φ)
    {G : MeasurableSpace E} (hG : G ≤ mE) {H : MeasurableSpace Ω}
    (hGH : MeasurableSpace.comap Φ G ≤ H) (hH : H ≤ mΩ)
    (f : E → ℝ) (hf : Integrable f ((@Measure.map Ω E mΩ mE Φ P))) (p : ℝ)
    (hp : ∀ᵐ ω ∂P, p ≤ P[fun ω => f (Φ ω) | H] ω) :
    ∀ᵐ x ∂((@Measure.map Ω E mΩ mE Φ P)), p ≤ ((@Measure.map Ω E mΩ mE Φ P))[f | G] x := by
  have hpull := condExp_const_le_of_le_of_condExp_const_le hGH hH hp
  have heq := @condExp_comap_map Ω E mΩ G mE hG P (inferInstance) Φ hΦ f hf
  have hbound : ∀ᵐ ω ∂P, p ≤ ((@Measure.map Ω E mΩ mE Φ P))[f | G] (Φ ω) := by
    filter_upwards [hpull, heq] with ω hω he
    exact he ▸ hω
  have hmeas : @MeasurableSet E mE {x | p ≤ ((@Measure.map Ω E mΩ mE Φ P))[f | G] x} :=
    measurableSet_le measurable_const (stronglyMeasurable_condExp.measurable.mono hG le_rfl)
  let _ : MeasurableSpace E := mE
  let _ : MeasurableSpace Ω := mΩ
  exact (ae_map_iff hΦ.aemeasurable hmeas).2 hbound

end LatticeProb
