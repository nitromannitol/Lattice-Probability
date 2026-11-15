import LatticeProb.LQG.CoupledAreaClockPath
import LatticeProb.Topology.ContinuousMapBorel

/-! # Measurable Brownian paths under the area clock -/

set_option autoImplicit false

open MeasureTheory Set MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace LatticeProb

/-- Composition of measurable random continuous paths is a measurable random
continuous path, even when the two paths depend on the same sample. -/
theorem measurable_random_path_comp {Ω : Type} [MeasurableSpace Ω]
    (X : Ω → C(ℝ, ℝ × ℝ)) (F : Ω → C(ℝ, ℝ))
    (hX : Measurable X) (hF : Measurable F) :
    Measurable (fun ω => (X ω).comp (F ω)) := by
  apply ContinuousMap.measurable_iff_eval.2
  intro t
  exact continuous_eval.measurable.comp
    (hX.prodMk ((ContinuousMap.measurable_eval t).comp hF))

/-- The coupled area clock and the Brownian path composed with it have
measurable continuous versions, agreeing simultaneously at every time with
an order-isomorphism clock on a single full-measure event. -/
theorem exists_measurable_coupled_clocked_brownian_path
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P) :
    ∃ (F : Ω → C(ℝ, ℝ)) (G : Ω → Path2), Measurable F ∧ Measurable G ∧
      ∀ᵐ ω ∂P, ∃ ψ : ℝ ≃o ℝ, ψ 0 = 0 ∧
        (∀ t, η₀ ω t = η ω (ψ t)) ∧
        (∀ t, F ω t = ψ t) ∧ ∀ t, G ω t = bm ω (ψ t) := by
  obtain ⟨F, hF, hclock⟩ := exists_measurable_coupled_area_clock_path hC hγ hf
  refine ⟨F, fun ω => (bm ω).comp (F ω), hF,
    measurable_random_path_comp bm F hC.measurable_curves.2.2.2 hF, ?_⟩
  filter_upwards [hclock] with ω hω
  obtain ⟨ψ, h0, hη, hψ⟩ := hω
  exact ⟨ψ, h0, hη, hψ, fun t => by simp [hψ t]⟩

end LatticeProb
