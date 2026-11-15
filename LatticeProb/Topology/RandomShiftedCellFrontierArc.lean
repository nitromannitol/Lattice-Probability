import LatticeProb.Topology.RandomCurveSegmentFrontierArc
import LatticeProb.Topology.CompactCurveRange

/-! # Shared frontier arcs of randomly shifted curve cells -/

set_option autoImplicit false

open Set MeasureTheory
open scoped unitInterval

namespace LatticeProb

/-- For measurable random curves, meshes and shifts, the event that two labelled
shifted cells share an injective frontier path is null measurable under a finite law. -/
theorem nullMeasurableSet_exists_injective_path_in_random_shifted_cell_frontiers
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] (B : ι → Set ℂ)
    (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ) (k l : ℤ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (hopen : ∀ i, IsOpen (B i))
    (hbasis : ∀ (V : Set ℂ), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω | ∃ γ : C(unitInterval, ℂ), Function.Injective γ ∧
      (∀ t, γ t ∈ frontier (shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ)) ∧
      (∀ t, γ t ∈ frontier (shiftedCompactCell (η ω) (ε ω) (θ ω) l : Set ℂ))} μ := by
  have ha (j : ℤ) : Measurable (fun ω => ε ω * ((j : ℝ) - 1 + θ ω)) :=
    hε.mul (measurable_const.add hθ)
  have hb (j : ℤ) : Measurable (fun ω => ε ω * ((j : ℝ) + θ ω)) :=
    hε.mul (measurable_const.add hθ)
  simpa only [coe_shiftedCompactCell] using
    nullMeasurableSet_exists_injective_path_in_random_curve_segment_frontiers B η
      (fun ω => ε ω * ((k : ℝ) - 1 + θ ω)) (fun ω => ε ω * ((k : ℝ) + θ ω))
      (fun ω => ε ω * ((l : ℝ) - 1 + θ ω)) (fun ω => ε ω * ((l : ℝ) + θ ω))
      hη (ha k) (hb k) (ha l) (hb l) hopen hbasis μ

end LatticeProb
