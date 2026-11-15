import LatticeProb.Topology.ComponentIntervalWitness

/-! # Strict interval witnesses for curve components -/

set_option autoImplicit false

open Set MeasureTheory Topology

namespace LatticeProb

/-- Existence of a bounded, nondegenerate component interval is analytic. -/
theorem analyticSet_exists_strict_bounded_component_interval (s t : ℝ) :
    AnalyticSet {p : C(ℝ, ℂ) × ℂ | ∃ a b : ℝ, s ≤ a ∧ a < b ∧ b ≤ t ∧
      closure (connectedComponentIn (interior (p.1 '' Icc s t)) p.2) =
        p.1 '' Icc a b} := by
  have : PolishSpace C(ℝ, ℂ) := LQGMetric.polishSpace_continuousMap ℝ ℂ
  let E : Set ((C(ℝ, ℂ) × ℂ) × (ℝ × ℝ)) := {p |
    s ≤ p.2.1 ∧ p.2.1 ≤ p.2.2 ∧ p.2.2 ≤ t ∧
      closure (connectedComponentIn (interior (p.1.1 '' Icc s t)) p.1.2) =
        p.1.1 '' Icc p.2.1 p.2.2}
  let D : Set ((C(ℝ, ℂ) × ℂ) × (ℝ × ℝ)) := {p | p.2.1 < p.2.2}
  have hE : MeasurableSet E := measurableSet_bounded_component_interval s t
  have hD : MeasurableSet D :=
    measurableSet_lt (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
  have heq : {p : C(ℝ, ℂ) × ℂ | ∃ a b : ℝ, s ≤ a ∧ a < b ∧ b ≤ t ∧
      closure (connectedComponentIn (interior (p.1 '' Icc s t)) p.2) =
        p.1 '' Icc a b} = Prod.fst '' (E ∩ D) := by
    ext p
    constructor
    · rintro ⟨a, b, ha, hab, hb, he⟩
      exact ⟨(p, (a, b)), ⟨⟨ha, le_of_lt hab, hb, he⟩, hab⟩, rfl⟩
    · rintro ⟨⟨q, a, b⟩, ⟨⟨ha, _, hb, he⟩, hab⟩, rfl⟩
      exact ⟨a, b, ha, hab, hb, he⟩
  rw [heq]
  exact (hE.inter hD).analyticSet.image_of_continuous continuous_fst

/-- The strict bounded component witness event is null-measurable for any finite law. -/
theorem nullMeasurableSet_exists_strict_bounded_component_interval (s t : ℝ)
    (μ : Measure (C(ℝ, ℂ) × ℂ)) [IsFiniteMeasure μ] :
    NullMeasurableSet {p : C(ℝ, ℂ) × ℂ | ∃ a b : ℝ, s ≤ a ∧ a < b ∧ b ≤ t ∧
      closure (connectedComponentIn (interior (p.1 '' Icc s t)) p.2) =
        p.1 '' Icc a b} μ := by
  have : PolishSpace C(ℝ, ℂ) := LQGMetric.polishSpace_continuousMap ℝ ℂ
  exact AnalyticSet.nullMeasurableSet μ (analyticSet_exists_strict_bounded_component_interval s t)

end LatticeProb
