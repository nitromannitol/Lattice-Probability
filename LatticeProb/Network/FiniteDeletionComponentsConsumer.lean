import LatticeProb.Network.FiniteDeletionComponents
import LatticeProb.Network.BarrierMaximumConsumer

/-!
# Finite deletion on the infinite ray

The accepted natural-number ray has one actual infinite component. With the empty deleted
edge set, all hypotheses of the finite-exception theorem are proved for this infinite graph.
-/

namespace LatticeProb.Network.Ray

open SimpleGraph

/-- Every component of the ray after empty deletion has all natural numbers as support. -/
theorem empty_deletion_component_supp
    (C : (graph.deleteEdges ∅).ConnectedComponent) : C.supp = Set.univ := by
  apply Set.eq_univ_of_forall
  intro n
  obtain ⟨m, hm⟩ := C.nonempty_supp
  apply (ConnectedComponent.mem_supp_iff C n).mpr
  calc
    (graph.deleteEdges ∅).connectedComponentMk n =
        (graph.deleteEdges ∅).connectedComponentMk m := by
      apply ConnectedComponent.sound
      simpa only [deleteEdges_empty] using graph_connected.preconnected n m
    _ = C := (ConnectedComponent.mem_supp_iff C m).mp hm

/-- Empty deletion on the infinite ray has a unique infinite component, with no assumed
uniqueness or infinitude hypothesis. -/
theorem empty_deletion_unique_infinite :
    ∃! C : (graph.deleteEdges ∅).ConnectedComponent, C.supp.Infinite := by
  refine ⟨(graph.deleteEdges ∅).connectedComponentMk 0, ?_, ?_⟩
  · dsimp only
    rw [empty_deletion_component_supp]
    exact Set.infinite_univ
  · intro C _
    apply ConnectedComponent.supp_injective
    rw [empty_deletion_component_supp, empty_deletion_component_supp]

/-- The generic finite-exception result applies to the actual unique infinite component
of the ray after empty deletion. -/
theorem empty_deletion_finite_exceptions :
    ((graph.deleteEdges ∅).connectedComponentMk 0).suppᶜ.Finite := by
  obtain ⟨K, hK, hunique⟩ := empty_deletion_unique_infinite
  have hzero : (graph.deleteEdges ∅).connectedComponentMk 0 = K := by
    apply hunique
    rw [empty_deletion_component_supp]
    exact Set.infinite_univ
  rw [hzero]
  exact finite_compl_of_unique_infinite_component graph_connected Set.finite_empty K hK
    (fun C hC => hunique C hC)

end LatticeProb.Network.Ray
