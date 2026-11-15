import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.UnitInterval

/-! # Components containing shared frontier arcs -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped unitInterval

namespace LatticeProb

/-- A shared injective frontier path of two closed sets is contained in a
non-singleton component of their intersection. -/
theorem exists_nonSingleton_inter_component_of_shared_frontier_arc
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (p : C(unitInterval, X))
    (hp : Function.Injective p)
    (hAp : ∀ t, p t ∈ frontier A) (hBp : ∀ t, p t ∈ frontier B) :
    ∃ C ∈ connectedComponentIn (A ∩ B) '' (A ∩ B),
      ¬ C.Subsingleton ∧ Set.range p ⊆ C := by
  have hsub : Set.range p ⊆ A ∩ B := by
    rintro x ⟨t, rfl⟩
    exact ⟨hA.frontier_subset (hAp t), hB.frontier_subset (hBp t)⟩
  have hp0 : p 0 ∈ Set.range p := ⟨0, rfl⟩
  have hp1 : p 1 ∈ Set.range p := ⟨1, rfl⟩
  have hcomponent : Set.range p ⊆ connectedComponentIn (A ∩ B) (p 0) :=
    (isPreconnected_range p.continuous).subset_connectedComponentIn hp0 hsub
  refine ⟨_, ⟨p 0, hsub hp0, rfl⟩, ?_, hcomponent⟩
  intro hs
  have h01 : (0 : unitInterval) = 1 := hp (hs (hcomponent hp0) (hcomponent hp1))
  exact zero_ne_one h01

end LatticeProb
