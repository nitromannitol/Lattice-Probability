import LatticeProb.Network.Dirichlet
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Unit Laplacians under finite edge removal

Deleting unordered edges partitions each neighbor finset into retained and removed neighbors.
The difference of the two unit Laplacians is exactly the sum of increments over removed
incident edges. Harmonic functions on the two actual graphs therefore satisfy a signed
forcing equation on the original graph; connectedness is unnecessary for this algebra.
-/

open scoped BigOperators Classical

namespace LatticeProb.Network

variable {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]

/-- Edge deletion preserves local finiteness, by inclusion of each neighbor set. -/
noncomputable instance deleteEdgesLocallyFinite (B : Finset (Sym2 V)) :
    (G.deleteEdges (B : Set (Sym2 V))).LocallyFinite := fun x =>
  Fintype.ofInjective
    (fun y : (G.deleteEdges (B : Set (Sym2 V))).neighborSet x =>
      (⟨y.1, (SimpleGraph.deleteEdges_adj.mp y.2).1⟩ : G.neighborSet x))
    (fun _ _ h => Subtype.ext (congrArg (fun z : G.neighborSet x => z.val) h))

/-- The neighbors joined to `x` by one of the removed unordered edges. -/
noncomputable def removedNeighbors (B : Finset (Sym2 V)) (x : V) : Finset V :=
  (G.neighborFinset x).filter fun y => s(x, y) ∈ B

/-- The actual deleted graph has precisely the retained neighbors. -/
theorem neighborFinset_deleteEdges (B : Finset (Sym2 V)) (x : V) :
    (G.deleteEdges (B : Set (Sym2 V))).neighborFinset x =
      (G.neighborFinset x).filter (fun y => s(x, y) ∉ B) := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj,
    Finset.mem_coe, Finset.mem_filter]

/-- Retained and removed neighbors exhaust the original neighbor finset. -/
theorem neighborFinset_partition (B : Finset (Sym2 V)) (x : V) :
    (G.deleteEdges (B : Set (Sym2 V))).neighborFinset x ∪ removedNeighbors G B x =
      G.neighborFinset x := by
  rw [neighborFinset_deleteEdges, removedNeighbors]
  ext y
  simp only [Finset.mem_union, Finset.mem_filter]
  tauto

/-- The neighbor partition is disjoint. -/
theorem disjoint_neighborFinset_removedNeighbors (B : Finset (Sym2 V)) (x : V) :
    Disjoint ((G.deleteEdges (B : Set (Sym2 V))).neighborFinset x)
      (removedNeighbors G B x) := by
  rw [neighborFinset_deleteEdges, removedNeighbors]
  exact Finset.disjoint_left.mpr fun y hy hz =>
    (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2

/-- Splitting the neighbor sum gives the original unit Laplacian as retained plus removed. -/
theorem netLaplacian_eq_deleteEdges_add (B : Finset (Sym2 V)) (f : V → ℝ) (x : V) :
    netLaplacian G (unitCond G) f x =
      netLaplacian (G.deleteEdges (B : Set (Sym2 V)))
        (unitCond (G.deleteEdges (B : Set (Sym2 V)))) f x +
      ∑ y ∈ removedNeighbors G B x, (f y - f x) := by
  rw [netLaplacian_unitCond, netLaplacian_unitCond,
    LatticeProb.Graph.laplacian, LatticeProb.Graph.laplacian]
  rw [← neighborFinset_partition G B x,
    Finset.sum_union (disjoint_neighborFinset_removedNeighbors G B x)]

/-- The signed difference of unit Laplacians is the removed incident-bond sum. -/
theorem netLaplacian_sub_deleteEdges (B : Finset (Sym2 V)) (f : V → ℝ) (x : V) :
    netLaplacian G (unitCond G) f x -
      netLaplacian (G.deleteEdges (B : Set (Sym2 V)))
        (unitCond (G.deleteEdges (B : Set (Sym2 V)))) f x =
      ∑ y ∈ removedNeighbors G B x, (f y - f x) := by
  rw [netLaplacian_eq_deleteEdges_add G B f x]
  exact add_sub_cancel_left _ _

/-- Harmonicity on the deleted graph makes the original Laplacian equal the removed sum. -/
theorem netLaplacian_of_harmonic_deleteEdges (B : Finset (Sym2 V)) (f : V → ℝ) (x : V)
    (hf : netLaplacian (G.deleteEdges (B : Set (Sym2 V)))
      (unitCond (G.deleteEdges (B : Set (Sym2 V)))) f x = 0) :
    netLaplacian G (unitCond G) f x =
      ∑ y ∈ removedNeighbors G B x, (f y - f x) := by
  rw [netLaplacian_eq_deleteEdges_add G B f x, hf, zero_add]

/-- If `u` and `u'` are harmonic on the respective graphs at `x`, their difference has
forcing equal to the negative removed-edge increments of `u'` on the original graph. -/
theorem netLaplacian_sub_of_harmonic_deleteEdges (B : Finset (Sym2 V))
    (u u' : V → ℝ) (x : V)
    (hu : netLaplacian G (unitCond G) u x = 0)
    (hu' : netLaplacian (G.deleteEdges (B : Set (Sym2 V)))
      (unitCond (G.deleteEdges (B : Set (Sym2 V)))) u' x = 0) :
    netLaplacian G (unitCond G) (fun y => u y - u' y) x =
      -(∑ y ∈ removedNeighbors G B x, (u' y - u' x)) := by
  rw [netLaplacian_sub, hu, netLaplacian_of_harmonic_deleteEdges G B u' x hu', zero_sub]

end LatticeProb.Network
