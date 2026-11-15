import LatticeProb.Topology.AreaCurveSimultaneousComponentIdentity

/-! # Component visit identities for countably many segments -/

set_option autoImplicit false

open Set MeasureTheory Function

namespace LatticeProb

/-- For countably many fixed segments of a proper area-parametrized curve, one
exceptional set of times works for every component and every interval witness. -/
theorem ae_component_visit_identity_countable_segments
    {ι : Type*} [Countable ι] (η : ℝ → ℂ) (μ : Measure ℂ) (hη : Continuous η)
    (hp : IsProperMap η) (hs : Surjective η) (hmap : Measure.map η volume = μ)
    (harea : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    (s t : ι → ℝ) (hst : ∀ i, s i < t i) :
    ∀ᵐ u ∂volume, ∀ i, ∀ x ∈ interior (η '' Icc (s i) (t i)), ∀ a b : ℝ, a < b →
      η '' Icc a b = closure (connectedComponentIn (interior (η '' Icc (s i) (t i))) x) →
      (η u ∈ connectedComponentIn (interior (η '' Icc (s i) (t i))) x ↔ u ∈ Ioo a b) := by
  exact ae_all_iff.mpr fun i =>
    ae_component_visit_identity_of_proper_area_curve η μ hη hp hs hmap harea (hst i)

end LatticeProb
