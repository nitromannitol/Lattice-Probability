import LatticeProb.Topology.AreaCurveIntervalContainment
import LatticeProb.Topology.ComponentVisitEndpoints
import LatticeProb.Topology.ComponentIntervalWitness

/-! # Interval witnesses for components of area-parametrized curves -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- An interval tracing the closure of a nonempty component of a segment image
is contained in the original interval. -/
theorem component_interval_bounds_of_area_curve
    (f : C(ℝ, ℂ)) (μ : Measure ℂ) (x : ℂ) (s t a b : ℝ)
    (hst : s < t)
    (hmass : ∀ u v : ℝ, u < v → μ (f '' Icc u v) = ENNReal.ofReal (v - u))
    (hne : (connectedComponentIn (interior (f '' Icc s t)) x).Nonempty)
    (himage : f '' Icc a b = closure (connectedComponentIn (interior (f '' Icc s t)) x)) :
    s ≤ a ∧ a < b ∧ b ≤ t := by
  let U := connectedComponentIn (interior (f '' Icc s t)) x
  have hU : IsOpen U := isOpen_interior.connectedComponentIn
  have hab : a < b := interval_lt_of_image_eq_closure_open f U a b hU hne himage
  have hsub : f '' Icc a b ⊆ f '' Icc s t := by
    rw [himage]
    exact closure_minimal ((connectedComponentIn_subset _ _).trans interior_subset)
      (isCompact_Icc.image f.continuous).isClosed
  have hbounds := Icc_subset_of_area_curve_image_subset f μ f.continuous hmass hab hst hsub
  exact ⟨(hbounds ⟨le_rfl, hab.le⟩).1, hab, (hbounds ⟨hab.le, le_rfl⟩).2⟩

/-- Interval-image existence for a nonempty component transfers through equality
of curve-and-point laws when the source curve is area-parametrized. -/
theorem ae_exists_bounded_component_interval_of_area_curve_map_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsFiniteMeasure P] (P' : Measure Ω')
    (V : Ω → C(ℝ, ℂ) × ℂ) (V' : Ω' → C(ℝ, ℂ) × ℂ)
    (μ : Ω → Measure ℂ)
    (hV : Measurable V) (hV' : Measurable V') (hlaw : P'.map V' = P.map V)
    (s t : ℝ) (hst : s < t)
    (harea : ∀ᵐ ω ∂P, ∀ u v : ℝ, u < v →
      μ ω ((V ω).1 '' Icc u v) = ENNReal.ofReal (v - u))
    (hcomponent : ∀ᵐ ω ∂P,
      (connectedComponentIn (interior ((V ω).1 '' Icc s t)) (V ω).2).Nonempty ∧
      ∃ a b : ℝ, (V ω).1 '' Icc a b =
        closure (connectedComponentIn (interior ((V ω).1 '' Icc s t)) (V ω).2)) :
    ∀ᵐ ω ∂P', ∃ a b : ℝ, s ≤ a ∧ a ≤ b ∧ b ≤ t ∧
      closure (connectedComponentIn (interior ((V' ω).1 '' Icc s t)) (V' ω).2) =
        (V' ω).1 '' Icc a b := by
  apply ae_exists_bounded_component_interval_of_map_eq P P' V V' hV hV' hlaw s t
  filter_upwards [harea, hcomponent] with ω hmass hc
  obtain ⟨hne, a, b, himage⟩ := hc
  obtain ⟨ha, hab, hb⟩ := component_interval_bounds_of_area_curve
    (V ω).1 (μ ω) (V ω).2 s t a b hst hmass hne himage
  exact ⟨a, b, ha, hab.le, hb, himage.symm⟩

end LatticeProb
