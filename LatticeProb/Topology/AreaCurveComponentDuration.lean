import LatticeProb.Topology.AreaComponentWitnessTransfer
import LatticeProb.Topology.AreaCurveSimultaneousComponentIdentity

/-! # Durations of component visits for area-parametrized curves -/

set_option autoImplicit false

open Set MeasureTheory Function

namespace LatticeProb

/-- Each interval witnessing a component closure has the component's area as
its duration. On one common conull set of times, visits to every such component
occur exactly during its witnessing interval. -/
theorem component_duration_and_ae_visits_of_proper_area_curve
    (η : C(ℝ, ℂ)) (μ : Measure ℂ)
    (hp : IsProperMap η) (hs : Surjective η) (hmap : Measure.map η volume = μ)
    (harea : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {s t : ℝ} (hst : s < t) :
    (∀ x ∈ interior (η '' Icc s t), ∀ a b : ℝ,
      η '' Icc a b = closure (connectedComponentIn (interior (η '' Icc s t)) x) →
      s ≤ a ∧ a < b ∧ b ≤ t ∧
        μ (connectedComponentIn (interior (η '' Icc s t)) x) = ENNReal.ofReal (b - a)) ∧
    ∀ᵐ u ∂volume, ∀ x ∈ interior (η '' Icc s t), ∀ a b : ℝ,
      η '' Icc a b = closure (connectedComponentIn (interior (η '' Icc s t)) x) →
      (η u ∈ connectedComponentIn (interior (η '' Icc s t)) x ↔ u ∈ Ioo a b) := by
  have hfront : μ (frontier (η '' Icc s t)) = 0 :=
    measure_frontier_image_Icc_eq_zero_of_proper η μ η.continuous hp hs harea hst
  have hbounds : ∀ x ∈ interior (η '' Icc s t), ∀ a b : ℝ,
      η '' Icc a b = closure (connectedComponentIn (interior (η '' Icc s t)) x) →
      s ≤ a ∧ a < b ∧ b ≤ t := by
    intro x hx a b hi
    exact component_interval_bounds_of_area_curve η μ x s t a b hst harea
      ⟨x, mem_connectedComponentIn hx⟩ hi
  constructor
  · intro x hx a b hi
    obtain ⟨ha, hab, hb⟩ := hbounds x hx a b hi
    have hzero := measure_frontier_component_interior_eq_zero
      (isCompact_Icc.image η.continuous).isClosed μ hfront x
    refine ⟨ha, hab, hb, ?_⟩
    calc
      μ (connectedComponentIn (interior (η '' Icc s t)) x) =
          μ (closure (connectedComponentIn (interior (η '' Icc s t)) x)) :=
        (measure_closure_of_null_frontier hzero).symm
      _ = μ (η '' Icc a b) := congrArg μ hi.symm
      _ = ENNReal.ofReal (b - a) := harea a b hab
  · have h := ae_component_visit_identity_of_proper_area_curve η μ η.continuous hp hs hmap
      harea hst
    filter_upwards [h] with u hu x hx a b hi
    exact hu x hx a b (hbounds x hx a b hi).2.1 hi

end LatticeProb
