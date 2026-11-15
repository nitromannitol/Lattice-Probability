import LatticeProb.Topology.MeasurableCurveComponentSecondCountable
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # Measurability of closures of random curve components -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace LatticeProb

/-- Closure membership for a random open set is measurable if membership at a
countable dense family of points and the selected point are measurable. -/
theorem measurableSet_mem_closure_of_open
    {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    [SecondCountableTopology E] [Nonempty E] [MeasurableSpace E] [BorelSpace E]
    (U : Ω → Set E) (y : Ω → E) (hU : ∀ ω, IsOpen (U ω))
    (hy : Measurable y)
    (hmem : ∀ n : ℕ, MeasurableSet {ω | denseSeq E n ∈ U ω}) :
    MeasurableSet {ω | y ω ∈ closure (U ω)} := by
  have hcl (ω : Ω) : closure (U ω) = closure (range (denseSeq E) ∩ U ω) := by
    apply Subset.antisymm
    · apply closure_minimal _ isClosed_closure
      simpa only [inter_comm] using (denseRange_denseSeq E).open_subset_closure_inter (hU ω)
    · exact closure_mono inter_subset_right
  have heq : {ω | y ω ∈ closure (U ω)} = ⋂ n : ℕ, ⋃ k : ℕ,
      ({ω | denseSeq E k ∈ U ω} ∩
       {ω | dist (y ω) (denseSeq E k) < 1 / ((n : ℝ) + 1)}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_inter_iff]
    rw [hcl ω, Metric.mem_closure_iff]
    constructor
    · intro h n
      have hn : 0 < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨z, ⟨⟨k, rfl⟩, hz⟩, hd⟩ := h _ hn
      exact ⟨k, hz, hd⟩
    · intro h ε hε
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      obtain ⟨k, hk, hd⟩ := h n
      exact ⟨denseSeq E k, ⟨⟨k, rfl⟩, hk⟩, hd.trans hn⟩
  rw [heq]
  exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun k =>
    (hmem k).inter (measurableSet_lt (hy.dist measurable_const) measurable_const)

/-- Membership in the closure of the component of a compact curve image's
interior is measurable jointly in the curve and both selected points. -/
theorem measurableSet_mem_closure_component_interior_image
    {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    [SecondCountableTopology E] [LocallyConnectedSpace E] [Nonempty E]
    [MeasurableSpace E] [BorelSpace E]
    (f : Ω → C(ℝ, E)) (x y : Ω → E) {K : Set ℝ}
    (hK : IsCompact K) (hf : Measurable f) (hx : Measurable x) (hy : Measurable y) :
    MeasurableSet {ω | y ω ∈ closure
      (connectedComponentIn (interior (f ω '' K)) (x ω))} := by
  apply measurableSet_mem_closure_of_open _ y (fun _ => isOpen_interior.connectedComponentIn) hy
  intro n
  exact measurableSet_mem_component_interior_image_of_locallyConnected f x
    (fun _ => denseSeq E n) hK hf hx measurable_const

end LatticeProb
