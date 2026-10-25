import LatticeProb.Network.FiniteEdgeRemoval
import Mathlib.Tactic.FinCases

/-!
# A finite graph sign check for edge removal

On the complete graph with two vertices, deleting its single edge leaves two isolated vertices.
The function with values zero and one is harmonic on the deleted graph, while its difference
from the zero harmonic function has original-graph Laplacian minus one at vertex zero.
-/

open scoped BigOperators Classical

namespace LatticeProb.Network

/-- The unique neighbor of zero in the two-vertex complete graph is one. -/
theorem top_two_neighborFinset_zero :
    (⊤ : SimpleGraph (Fin 2)).neighborFinset 0 = {1} := by
  ext y
  fin_cases y <;> simp [SimpleGraph.mem_neighborFinset]

/-- Removing the single edge of the two-vertex graph removes the neighbor of zero. -/
theorem top_two_removedNeighbors_zero :
    removedNeighbors (⊤ : SimpleGraph (Fin 2)) {s(0, 1)} 0 = {1} := by
  rw [removedNeighbors, top_two_neighborFinset_zero]
  simp only [Finset.filter_singleton, Finset.mem_singleton, ↓reduceIte]

/-- The vertex zero is isolated after deletion of the unique edge. -/
theorem top_two_deleted_neighborFinset_zero :
    ((⊤ : SimpleGraph (Fin 2)).deleteEdges
      ({s(0, 1)} : Finset (Sym2 (Fin 2)))).neighborFinset 0 = ∅ := by
  rw [neighborFinset_deleteEdges, top_two_neighborFinset_zero]
  simp only [Finset.filter_singleton, Finset.mem_singleton, not_true_eq_false, ↓reduceIte]

/-- The nonconstant function `v ↦ v.val` is harmonic at zero on the deleted graph. -/
theorem top_two_deleted_harmonic_zero :
    netLaplacian ((⊤ : SimpleGraph (Fin 2)).deleteEdges
      ({s(0, 1)} : Finset (Sym2 (Fin 2))))
      (unitCond ((⊤ : SimpleGraph (Fin 2)).deleteEdges
        ({s(0, 1)} : Finset (Sym2 (Fin 2))))) (fun v => (v.val : ℝ)) 0 = 0 := by
  rw [netLaplacian, top_two_deleted_neighborFinset_zero, Finset.sum_empty]

/-- A nonzero forcing consumer: `u = 0`, `u'(v) = v.val`, so `Δ_G(u-u')(0) = -1`.
This applies the general harmonic-difference theorem, including both harmonicity premises. -/
theorem top_two_edge_removal_forcing :
    netLaplacian (⊤ : SimpleGraph (Fin 2)) (unitCond ⊤)
      (fun v => (0 : ℝ) - (v.val : ℝ)) 0 = -1 := by
  have hu : netLaplacian (⊤ : SimpleGraph (Fin 2)) (unitCond ⊤)
      (fun _ => (0 : ℝ)) 0 = 0 := by
    simp only [netLaplacian, sub_self, mul_zero, Finset.sum_const_zero]
  rw [netLaplacian_sub_of_harmonic_deleteEdges (⊤ : SimpleGraph (Fin 2))
    {s(0, 1)} (fun _ => (0 : ℝ)) (fun v => (v.val : ℝ)) 0 hu
    top_two_deleted_harmonic_zero, top_two_removedNeighbors_zero]
  norm_num

end LatticeProb.Network
