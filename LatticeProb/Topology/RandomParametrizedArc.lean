import LatticeProb.Topology.CompactImagesArcWitness
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-! # Common arcs in random parametrized compact sets -/

set_option autoImplicit false

open Set MeasureTheory Topology
open scoped unitInterval

namespace LatticeProb

/-- Two measurable random continuous parametrizations have a null-measurable
common injective arc event under any finite law. -/
theorem nullMeasurableSet_exists_injective_path_in_random_curve_ranges
    {Ω : Type*} [MeasurableSpace Ω] (α β : Ω → C(unitInterval, ℂ))
    (hα : Measurable α) (hβ : Measurable β)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω | ∃ γ : C(unitInterval, ℂ), Function.Injective γ ∧
      (∀ t, ∃ x, γ t = α ω x) ∧ (∀ t, ∃ x, γ t = β ω x)} μ := by
  let J := unitInterval
  let P := C(J, ℂ) × C(J, ℂ)
  have : PolishSpace C(J, ℂ) := LQGMetric.polishSpace_continuousMap J ℂ
  have ha : AnalyticSet {p : P | ∃ γ : C(J, ℂ), Function.Injective γ ∧
      (∀ t, ∃ x, γ t = p.1 x) ∧ (∀ t, ∃ x, γ t = p.2 x)} := by
    apply analyticSet_exists_injective_path_in_compact_images
      (fun p : P × J => (p.1 : C(J, ℂ) × C(J, ℂ)).1 p.2)
      (fun p : P × J => (p.1 : C(J, ℂ) × C(J, ℂ)).2 p.2)
    · dsimp only [P]
      fun_prop
    · dsimp only [P]
      fun_prop
  let f : Ω → P := fun ω => (α ω, β ω)
  have hf : Measurable f := hα.prodMk hβ
  let : IsFiniteMeasure (μ.map f) := μ.isFiniteMeasure_map f
  exact (AnalyticSet.nullMeasurableSet (μ.map f) ha).preimage (hf.quasiMeasurePreserving μ)

end LatticeProb
