import LatticeProb.Topology.AreaComponentWitnessTransfer

/-! # Component interval witnesses at fixed curve times -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Equality of curve laws transfers bounded interval witnesses for the component
selected by evaluation at a fixed time, assuming the source has area parametrization
and the asserted component interval representation. -/
theorem ae_exists_bounded_component_interval_at_time_of_curve_map_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsFiniteMeasure P] (P' : Measure Ω')
    (F : Ω → C(ℝ, ℂ)) (F' : Ω' → C(ℝ, ℂ)) (μ : Ω → Measure ℂ)
    (hF : Measurable F) (hF' : Measurable F') (hlaw : P'.map F' = P.map F)
    (s t u : ℝ) (hst : s < t)
    (harea : ∀ᵐ ω ∂P, ∀ a b : ℝ, a < b →
      μ ω (F ω '' Icc a b) = ENNReal.ofReal (b - a))
    (hcomponent : ∀ᵐ ω ∂P,
      (connectedComponentIn (interior (F ω '' Icc s t)) (F ω u)).Nonempty ∧
      ∃ a b : ℝ, F ω '' Icc a b =
        closure (connectedComponentIn (interior (F ω '' Icc s t)) (F ω u))) :
    ∀ᵐ ω ∂P', ∃ a b : ℝ, s ≤ a ∧ a ≤ b ∧ b ≤ t ∧
      closure (connectedComponentIn (interior (F' ω '' Icc s t)) (F' ω u)) =
        F' ω '' Icc a b := by
  let φ : C(ℝ, ℂ) → C(ℝ, ℂ) × ℂ := fun f => (f, f u)
  have hφ : Measurable φ := measurable_id.prodMk (continuous_eval_const u).measurable
  have hp : Measurable (fun ω => φ (F ω)) := hφ.comp hF
  have hp' : Measurable (fun ω => φ (F' ω)) := hφ.comp hF'
  have hlaw' := MeasureTheory.map_comp_of_map_eq hF hF' hlaw hφ
  exact ae_exists_bounded_component_interval_of_area_curve_map_eq
    P P' (fun ω => φ (F ω)) (fun ω => φ (F' ω)) μ hp hp' hlaw' s t hst harea hcomponent

end LatticeProb
