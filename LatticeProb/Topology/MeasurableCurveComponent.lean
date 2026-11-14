import LatticeProb.Topology.MeasurableConnectedComponent
import LatticeProb.LQG.MatingOfTreesCouplingPathwise

/-! # Components of the interior of a compact curve image -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Membership in the component of a point in the interior of a compact curve image is
measurable, for measurable curves and points in a space with a countable connected basis. -/
theorem measurableSet_mem_connectedComponentIn_interior_image
    {Ω E ι : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [T2Space E]
    [TopologicalSpace.SeparableSpace E] [MeasurableSpace E] [BorelSpace E] [Countable ι]
    (B : ι → Set E) (f : Ω → C(ℝ, E)) (x y : Ω → E) {K : Set ℝ}
    (hK : IsCompact K) (hf : Measurable f) (hx : Measurable x) (hy : Measurable y)
    (hopen : ∀ i, IsOpen (B i)) (hconn : ∀ i, IsPreconnected (B i))
    (hbasis : ∀ (V : Set E), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V) :
    MeasurableSet {ω | y ω ∈ connectedComponentIn (interior (f ω '' K)) (x ω)} := by
  apply measurableSet_mem_connectedComponentIn B (fun ω => interior (f ω '' K)) x y
    hopen hconn hbasis (fun _ => isOpen_interior)
  · intro i
    have heq : {ω | B i ⊆ interior (f ω '' K)} = {ω | B i ⊆ f ω '' K} := by
      ext ω
      exact ⟨fun h => h.trans interior_subset, fun h => interior_maximal h (hopen i)⟩
    rw [heq]
    exact (ContinuousMap.measurableSet_setOf_subset_image (hopen i) hK).preimage hf
  · intro i
    exact (hopen i).measurableSet.preimage hx
  · intro i
    exact (hopen i).measurableSet.preimage hy

end LatticeProb
