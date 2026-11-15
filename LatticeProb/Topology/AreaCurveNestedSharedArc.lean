import LatticeProb.Topology.AreaCurveSharedFrontier

/-! # Arcs in nested segments of area-parametrized curves -/

set_option autoImplicit false

open Set MeasureTheory Function
open scoped unitInterval

namespace LatticeProb

/-- An arc shared by images of subsets of two ordered segments lies on the
shared frontier of the full segments of a proper area-parametrized curve. -/
theorem shared_frontier_arc_of_nested_segment_images
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (η : ℝ → X) (μ : Measure X)
    (hc : Continuous η) (hp : IsProperMap η) (hs : Surjective η)
    (hmap : Measure.map η volume = μ)
    (hμ : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {a b c d : ℝ} (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    {A B : Set ℝ} (hA : A ⊆ Icc a b) (hB : B ⊆ Icc c d)
    (p : C(unitInterval, X)) (hp_inj : Injective p)
    (hp_mem : ∀ t, p t ∈ η '' A ∩ η '' B) :
    ∃ q : C(unitInterval, X), Injective q ∧
      (∀ t, q t ∈ frontier (η '' Icc a b)) ∧
      (∀ t, q t ∈ frontier (η '' Icc c d)) := by
  refine ⟨p, hp_inj, ?_, ?_⟩
  all_goals
    intro t
    have h : p t ∈ η '' Icc a b ∩ η '' Icc c d :=
      ⟨image_mono hA (hp_mem t).1, image_mono hB (hp_mem t).2⟩
    rw [proper_area_curve_inter_eq_shared_frontier η μ hc hp hs hmap hμ hab hbc hcd] at h
    first | exact h.1 | exact h.2

end LatticeProb
