import LatticeProb.Topology.CurveInteriorFubini
import LatticeProb.Topology.CurveSegmentFrontier
import LatticeProb.Topology.CurveComponentFrontier

/-! # Frontiers of components of random curve segments -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Fixed-time interior visits, a measure parametrization, and the segment mass
identity imply null frontiers for all components of the segment interior. -/
theorem ae_measure_frontier_curve_components_eq_zero
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) [SigmaFinite P] (B : ι → Set ℂ)
    (f : Ω → C(ℝ, ℂ)) (μ : Ω → Measure ℂ) (a b : ℝ)
    (hf : Measurable f) (hopen : ∀ i, IsOpen (B i))
    (hbasis : ∀ (V : Set ℂ), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V)
    (hfixed : ∀ t ∈ Ioo a b, ∀ᵐ ω ∂P, f ω t ∈ interior (f ω '' Icc a b))
    (hmap : ∀ᵐ ω ∂P, Measure.map (f ω) volume = μ ω)
    (hmass : ∀ᵐ ω ∂P, μ ω (f ω '' Icc a b) = volume (Icc a b)) :
    ∀ᵐ ω ∂P, ∀ x : ℂ,
      μ ω (frontier (connectedComponentIn (interior (f ω '' Icc a b)) x)) = 0 := by
  have hinterior := ae_ae_curve_mem_interior_image_of_fixed_time P B f a b hf hopen hbasis hfixed
  filter_upwards [hinterior, hmap, hmass] with ω hi hm hs
  have hnull := measure_frontier_curve_segment_eq_zero (f ω) (μ ω) a b
    (f ω).continuous hm hs hi
  intro x
  exact measure_frontier_component_interior_eq_zero
    (isCompact_Icc.image (f ω).continuous).isClosed (μ ω) hnull x

end LatticeProb
