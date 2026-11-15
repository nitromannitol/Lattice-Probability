import LatticeProb.Topology.ProperSegmentObservationEndpoints
import Mathlib.Topology.Connected.LocallyConnected

/-! # Observable endpoints of proper area curves -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- The endpoints of a component of a proper area-parametrized plane curve have
versions measurable from observations of the segment, when the component closure
is the image of the endpoint interval. -/
theorem exists_observable_endpoints_of_proper_plane_curve_component
    {Ω : Type*} [MeasurableSpace Ω]
    (obs : MeasurableSpace Ω) (P : Measure Ω)
    (f : Ω → C(ℝ, ℂ)) (μ : Ω → Measure ℂ) (x : Ω → ℂ)
    (s t : ℝ) (a b : Ω → ℝ) (hst : s < t)
    (hf : ∀ r ∈ Icc s t, @Measurable Ω ℂ obs _ (fun ω => f ω r))
    (hx : @Measurable Ω ℂ obs _ x)
    (harea : ∀ᵐ ω ∂P, IsProperMap (f ω) ∧ Function.Surjective (f ω) ∧
      ∀ p q : ℚ, p ≤ q → μ ω (f ω '' Icc (p : ℝ) q) = ENNReal.ofReal ((q : ℝ) - p))
    (hcomponent : ∀ᵐ ω ∂P,
      let U := connectedComponentIn (interior (f ω '' Icc s t)) (x ω)
      U.Nonempty ∧ f ω '' Icc (a ω) (b ω) = closure U) :
    ∃ a' b' : Ω → ℝ, @Measurable Ω ℝ obs _ a' ∧ @Measurable Ω ℝ obs _ b' ∧
      (∀ᵐ ω ∂P, a' ω = a ω ∧ b' ω = b ω) := by
  obtain ⟨B, hBsub, hBcount, hBbasis⟩ :=
    (TopologicalSpace.IsTopologicalBasis.isOpen_isPreconnected (α := ℂ)).exists_countable
  have : Countable B := hBcount.to_subtype
  apply exists_observable_endpoints_of_proper_curve_component obs P
    (fun i : B => i.val) f μ x s t a b hst hf hx
  · intro i
    exact (hBsub i.property).1
  · intro i
    exact (hBsub i.property).2
  · intro V hV z hz
    obtain ⟨U, hU, hzU, hUV⟩ := hBbasis.isOpen_iff.mp hV z hz
    exact ⟨⟨U, hU⟩, hzU, hUV⟩
  · exact harea
  · exact hcomponent

end LatticeProb
