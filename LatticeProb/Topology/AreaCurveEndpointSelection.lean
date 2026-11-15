import LatticeProb.Topology.AreaCurveJointWitnessEvent
import LatticeProb.Topology.ComponentEndpointSelection

/-! # Component endpoint selection for area-parametrized curves -/

set_option autoImplicit false

open Function MeasureTheory Set

namespace LatticeProb

/-- A full joint event of proper, area-parametrized curve witnesses with common
fibres yields measurable strict component interval endpoints. -/
theorem exists_measurable_component_endpoints_of_area_curve_witnesses
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure (X × C(ℝ, ℂ))) [IsFiniteMeasure μ]
    (ν : X × C(ℝ, ℂ) → Measure ℂ) (hν : Measurable ν)
    (R : X → ℝ → ℝ → Prop) (s u t : ℝ)
    (hR : NullMeasurableSet {p : X × C(ℝ, ℂ) |
      ∀ v w, p.2 v = p.2 w ↔ R p.1 v w} μ)
    (hfull : ∀ᵐ p ∂μ, (∀ v w, p.2 v = p.2 w ↔ R p.1 v w) ∧
      IsProperMap p.2 ∧ Surjective p.2 ∧
      p.2 u ∈ interior (p.2 '' Icc s t) ∧ IsFiniteMeasureOnCompacts (ν p) ∧
      (∀ v w : ℝ, v ≤ w → ν p (p.2 '' Icc v w) = ENNReal.ofReal (w - v)) ∧
      ∃ a b : ℝ, s ≤ a ∧ a < b ∧ b ≤ t ∧
        closure (connectedComponentIn (interior (p.2 '' Icc s t)) (p.2 u)) =
          p.2 '' Icc a b) :
    ∃ F : X → ℝ × ℝ, Measurable F ∧ ∀ᵐ p ∂μ,
      s ≤ (F p.1).1 ∧ (F p.1).1 < (F p.1).2 ∧ (F p.1).2 ≤ t ∧
      p.2 '' Icc (F p.1).1 (F p.1).2 =
        closure (connectedComponentIn (interior (p.2 '' Icc s t)) (p.2 u)) := by
  let A : Set (X × C(ℝ, ℂ)) := {p |
    (∀ v w, p.2 v = p.2 w ↔ R p.1 v w) ∧
    IsProperMap p.2 ∧ Surjective p.2 ∧
    p.2 u ∈ interior (p.2 '' Icc s t) ∧ IsFiniteMeasureOnCompacts (ν p) ∧
    (∀ v w : ℝ, v ≤ w → ν p (p.2 '' Icc v w) = ENNReal.ofReal (w - v)) ∧
    ∃ a b : ℝ, s ≤ a ∧ a < b ∧ b ≤ t ∧
      closure (connectedComponentIn (interior (p.2 '' Icc s t)) (p.2 u)) =
        p.2 '' Icc a b}
  have hA : NullMeasurableSet A μ :=
    nullMeasurableSet_area_curve_component_witness μ Prod.snd measurable_snd ν hν s u t _ hR
  apply exists_measurable_component_endpoints_of_joint_witnesses μ R s u t hA hfull
  intro p hp
  obtain ⟨hr, hp, hs, hi, _, hm, a, b, ha, hab, hb, he⟩ := hp
  exact ⟨hp, hs, hr, hi, ⟨ν p, fun v w hvw => hm v w (le_of_lt hvw)⟩,
    a, b, ha, hab, hb, he.symm⟩

end LatticeProb
