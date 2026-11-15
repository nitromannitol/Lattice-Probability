import LatticeProb.Topology.MeasurableCurveComponent
import Mathlib.Topology.Connected.LocallyConnected

/-! # Measurable components in locally connected spaces -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Membership in a component of the interior of a compact curve image is
measurable in any second-countable locally connected Hausdorff Borel space. -/
theorem measurableSet_mem_component_interior_image_of_locallyConnected
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [T2Space E]
    [SecondCountableTopology E] [LocallyConnectedSpace E] [MeasurableSpace E] [BorelSpace E]
    (f : Ω → C(ℝ, E)) (x y : Ω → E) {K : Set ℝ}
    (hK : IsCompact K) (hf : Measurable f) (hx : Measurable x) (hy : Measurable y) :
    MeasurableSet {ω | y ω ∈ connectedComponentIn (interior (f ω '' K)) (x ω)} := by
  obtain ⟨B, hBsub, hBcount, hBbasis⟩ :=
    (TopologicalSpace.IsTopologicalBasis.isOpen_isPreconnected (α := E)).exists_countable
  have : Countable B := hBcount.to_subtype
  apply measurableSet_mem_connectedComponentIn_interior_image
    (fun i : B => i.val) f x y hK hf hx hy
  · intro i
    exact (hBsub i.property).1
  · intro i
    exact (hBsub i.property).2
  · intro V hV z hz
    obtain ⟨U, hU, hzU, hUV⟩ := hBbasis.isOpen_iff.mp hV z hz
    exact ⟨⟨U, hU⟩, hzU, hUV⟩

end LatticeProb
