import LatticeProb.Network.FiniteBridgeRigidity

/-!
# Two-vertex finite bridge consumers

The nonconstant boundary values zero and one have finite-side Laplacian flux one.
A separate consumer applies the finite-component harmonic theorem to the same genuine
bridge. The deleted component is the singleton endpoint, rather than an empty set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical

namespace LatticeProb.Network

/-- Boundary data zero at `0` and one at `1` has outward finite-side flux one. -/
theorem finTwo_singleton_laplacian_flux :
    ∑ x ∈ ({0} : Finset (Fin 2)),
      netLaplacian (⊤ : SimpleGraph (Fin 2)) (unitCond ⊤)
        (fun y => (y.val : ℝ)) x = 1 := by
  classical
  have hn : (⊤ : SimpleGraph (Fin 2)).neighborFinset 0 = {1} := by
    ext y
    fin_cases y <;> simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.top_adj,
      Finset.mem_singleton] <;> decide
  rw [Finset.sum_singleton, netLaplacian, hn, Finset.sum_singleton]
  norm_num [unitCond]

/-- The actual graph after deleting the sole two-vertex edge is the empty graph. -/
theorem finTwo_delete_edge_eq_bot :
    (⊤ : SimpleGraph (Fin 2)).deleteEdges
      (({s(0, 1)} : Finset (Sym2 (Fin 2))) : Set (Sym2 (Fin 2))) = ⊥ := by
  classical
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [SimpleGraph.deleteEdges_adj]

/-- A harmonic function on the two-vertex top graph has zero bridge drop, by applying
finite-side flux to its actual finite deleted endpoint component. -/
theorem finTwo_harmonic_values_eq (u : Fin 2 → ℝ)
    (hu : ∀ x, netLaplacian (⊤ : SimpleGraph (Fin 2)) (unitCond ⊤) u x = 0) :
    u 0 = u 1 := by
  apply eq_of_harmonic_finite_deleted_component (⊤ : SimpleGraph (Fin 2))
    (a := 0) (b := 1) (by decide) (Set.toFinite _) ?_ u hu
  rw [finTwo_delete_edge_eq_bot, SimpleGraph.reachable_bot]
  decide

end LatticeProb.Network
