import LatticeProb.Prob.ExplorationCond

/-! # Conditional lower bounds and measurable realizations -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- A conditional lower bound on a law transfers through a measurable realization
and remains valid for any coarser conditioning sigma-algebra. -/
theorem conditional_lower_bound_of_map {Ω Ω' : Type*}
    {H : MeasurableSpace Ω} {G : MeasurableSpace Ω'}
    [mΩ : MeasurableSpace Ω] [m' : MeasurableSpace Ω'] (hG : G ≤ m')
    (P : Measure Ω) [IsFiniteMeasure P] (Φ : Ω → Ω') (hΦ : Measurable Φ)
    (hH : H ≤ MeasurableSpace.comap Φ G)
    (f : Ω' → ℝ) (hf : Integrable f (P.map Φ)) (p : ℝ)
    (hp : ∀ᵐ x ∂(P.map Φ), p ≤ (P.map Φ)[f | G] x) :
    ∀ᵐ ω ∂P, p ≤ P[fun ω => f (Φ ω) | H] ω := by
  have hGΦ : MeasurableSpace.comap Φ G ≤ (inferInstanceAs (MeasurableSpace Ω)) :=
    (MeasurableSpace.comap_mono hG).trans hΦ.comap_le
  have hH' := hH.trans hGΦ
  have hmap := condExp_comap_map hG P Φ hΦ f hf
  have hp' : ∀ᵐ ω ∂P, p ≤ P[fun ω => f (Φ ω) | MeasurableSpace.comap Φ G] ω := by
    filter_upwards [ae_of_ae_map hΦ.aemeasurable hp, hmap] with ω hω heq
    simpa only [heq] using hω
  have hmono := condExp_mono (m := H) (μ := P) (integrable_const p)
    (integrable_condExp) hp'
  have htower := condExp_condExp_of_le (μ := P) (f := fun ω => f (Φ ω)) hH hGΦ
  filter_upwards [hmono, htower] with ω hω heq
  simpa only [condExp_const hH', heq] using hω

end LatticeProb
