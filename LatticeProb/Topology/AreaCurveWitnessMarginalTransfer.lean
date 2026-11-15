import LatticeProb.Topology.AreaCurveJointWitnessEvent
import LatticeProb.Topology.SelectedComponentIntervalTransfer

/-! # Transfer of area-curve component endpoints -/

set_option autoImplicit false

open Function MeasureTheory Set

namespace LatticeProb

/-- Strict component endpoints selected from full area-curve witnesses transfer
through a common parameter marginal to proper surjective curves with the same fibres. -/
theorem exists_measurable_component_endpoints_of_area_curve_marginal_fibers
    {X Ω : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Ω] (μ : Measure (X × C(ℝ, ℂ))) [IsFiniteMeasure μ]
    (P : Measure Ω) (Z : Ω → X) (g : Ω → C(ℝ, ℂ))
    (hZ : Measurable Z) (hlaw : P.map Z = μ.map Prod.fst)
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
          p.2 '' Icc a b)
    (htarget : ∀ᵐ ω ∂P, IsProperMap (g ω) ∧ Surjective (g ω) ∧
      ∀ v w, g ω v = g ω w ↔ R (Z ω) v w) :
    ∃ F : X → ℝ × ℝ, Measurable F ∧
      (∀ᵐ p ∂μ, s ≤ (F p.1).1 ∧ (F p.1).1 < (F p.1).2 ∧ (F p.1).2 ≤ t ∧
        p.2 '' Icc (F p.1).1 (F p.1).2 =
          closure (connectedComponentIn (interior (p.2 '' Icc s t)) (p.2 u))) ∧
      (∀ᵐ ω ∂P, s ≤ (F (Z ω)).1 ∧ (F (Z ω)).1 < (F (Z ω)).2 ∧
        (F (Z ω)).2 ≤ t ∧ g ω '' Icc (F (Z ω)).1 (F (Z ω)).2 =
          closure (connectedComponentIn (interior (g ω '' Icc s t)) (g ω u))) := by
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
  apply exists_measurable_component_endpoints_of_marginal_fibers μ P Z g hZ hlaw R s u t
    hA hfull _ htarget
  intro p hp
  obtain ⟨hr, hp, hs, hi, _, hm, a, b, ha, hab, hb, he⟩ := hp
  exact ⟨hp, hs, hr, hi, ⟨ν p, fun v w hvw => hm v w (le_of_lt hvw)⟩,
    a, b, ha, hab, hb, he.symm⟩

end LatticeProb
