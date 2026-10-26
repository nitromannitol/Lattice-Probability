import LatticeProb.Prob.Percolation.LatticeBondInfiniteEvent
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Joint measurability of rooted harmonicity

The actual open-graph Laplacian is a finite sum over deterministic lattice neighbors,
with each summand retained exactly when its bond is open. This proves joint measurability
in the configuration and the ambient real function. Normalized harmonicity on the root
component is then a measurable relation, characterized on the actual component subtype.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open MeasureTheory
open scoped BigOperators Classical

variable {d : ℕ}

/-- Open neighbors are precisely the deterministic lattice neighbors whose bonds are open. -/
theorem openGraph_neighborFinset_eq_filter (ω : Configuration d) (x : Vertex d) :
    (openGraph ω).neighborFinset x =
      (nbrFinset x).filter (fun y => (openGraph ω).Adj x y) := by
  classical
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
  exact ⟨fun h => ⟨Graph.Zd.mem_nbrFinset.mpr
    (Graph.Zd.adj_iff.mp (openGraph_le ω h)), h⟩, And.right⟩

/-- The literal open-graph Laplacian equals the finite sum with open-bond indicators. -/
theorem laplacian_openGraph_eq_sum_ite (ω : Configuration d) (U : Vertex d → ℝ)
    (x : Vertex d) :
    Graph.laplacian (openGraph ω) U x =
      ∑ y ∈ nbrFinset x, if (openGraph ω).Adj x y then U y - U x else 0 := by
  classical
  rw [Graph.laplacian, openGraph_neighborFinset_eq_filter, Finset.sum_filter]

/-- For every fixed vertex, the actual neighbor-sum Laplacian is jointly measurable. -/
theorem measurable_laplacian_openGraph (x : Vertex d) :
    Measurable (fun z : Configuration d × (Vertex d → ℝ) =>
      Graph.laplacian (openGraph z.1) z.2 x) := by
  classical
  simp_rw [laplacian_openGraph_eq_sum_ite]
  apply Finset.measurable_sum
  intro y _
  exact Measurable.ite ((measurableSet_openGraph_adj x y).preimage measurable_fst)
    (((measurable_pi_apply y).comp measurable_snd).sub
      ((measurable_pi_apply x).comp measurable_snd)) measurable_const

/-- Normalization and harmonicity on the actual root component form a measurable relation. -/
theorem measurableSet_rooted_normalized_harmonic (o : Vertex d) :
    MeasurableSet {z : Configuration d × (Vertex d → ℝ) |
      z.2 o = 0 ∧ ∀ x, (openGraph z.1).Reachable o x →
        Graph.laplacian (openGraph z.1) z.2 x = 0} := by
  have hzero : MeasurableSet {z : Configuration d × (Vertex d → ℝ) | z.2 o = 0} :=
    measurableSet_eq_fun ((measurable_pi_apply o).comp measurable_snd) measurable_const
  have hpoint (x : Vertex d) :
      MeasurableSet {z : Configuration d × (Vertex d → ℝ) |
        (openGraph z.1).Reachable o x → Graph.laplacian (openGraph z.1) z.2 x = 0} := by
    simp only [imp_iff_not_or, Set.setOf_or]
    exact ((measurableSet_openGraph_reachable o x).preimage measurable_fst).compl.union
      (measurableSet_eq_fun (measurable_laplacian_openGraph x) measurable_const)
  have hforall : MeasurableSet {z : Configuration d × (Vertex d → ℝ) |
      ∀ x, (openGraph z.1).Reachable o x →
        Graph.laplacian (openGraph z.1) z.2 x = 0} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter hpoint
  exact hzero.inter hforall

/-- Restricting an ambient function to a component preserves its literal neighbor sum. -/
theorem componentLaplacian_restrict_eq {ω : Configuration d} (C : OpenComponent ω)
    (U : Vertex d → ℝ) (x : C) :
    componentLaplacian C (fun y => U y.val) x = Graph.laplacian (openGraph ω) U x.val := by
  classical
  unfold componentLaplacian Graph.laplacian
  apply Finset.sum_bij (fun y _ => y.val)
  · intro y hy
    apply (SimpleGraph.mem_neighborFinset _ _ _).mpr
    exact (SimpleGraph.mem_neighborFinset (componentGraph C) x y).mp hy
  · intro y _ z _ h
    exact Subtype.ext h
  · intro y hy
    have hadj := (SimpleGraph.mem_neighborFinset _ _ _).mp hy
    have hmem := C.mem_supp_of_adj_mem_supp x.property hadj
    exact ⟨⟨y, hmem⟩, (SimpleGraph.mem_neighborFinset _ _ _).mpr hadj, rfl⟩
  · intro y _
    rfl

/-- The ambient rooted relation is exactly normalized harmonicity of the restriction to
its actual component. Values outside the component are unrestricted on both sides. -/
theorem rooted_normalized_harmonic_iff (ω : Configuration d) (U : Vertex d → ℝ)
    (o : Vertex d) :
    (U o = 0 ∧ ∀ x, (openGraph ω).Reachable o x →
      Graph.laplacian (openGraph ω) U x = 0) ↔
    (let C := (openGraph ω).connectedComponentMk o
     (fun x : C => U x.val) ⟨o, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩ = 0 ∧
       ∀ x : C, componentLaplacian C (fun y => U y.val) x = 0) := by
  dsimp only
  constructor
  · rintro ⟨hzero, hharm⟩
    refine ⟨hzero, fun x => ?_⟩
    rw [componentLaplacian_restrict_eq]
    exact hharm x.val (((openGraph ω).connectedComponentMk o).reachable_of_mem_supp
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem x.property)
  · rintro ⟨hzero, hharm⟩
    refine ⟨hzero, fun x hx => ?_⟩
    have hmem : x ∈ ((openGraph ω).connectedComponentMk o).supp :=
      SimpleGraph.ConnectedComponent.mem_supp_iff _ _ |>.mpr
        (SimpleGraph.ConnectedComponent.sound hx.symm)
    exact (componentLaplacian_restrict_eq _ U ⟨x, hmem⟩) ▸ hharm ⟨x, hmem⟩

end LatticeProb.Percolation
