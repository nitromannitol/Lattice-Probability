import LatticeProb.Network.FiniteBoundaryUniqueness

/-!
# Boundary uniqueness on a finite path

The actual path `0 — 1 — 2` with unit conductances has the affine potential `v ↦ v / 2`.
Its interior vertex is harmonic, its terminal values are zero and one, and boundary
uniqueness determines it on all three vertices. Its nonconstancy invokes terminal separation.
-/

namespace LatticeProb.Network.FiniteBoundaryConsumers

open SimpleGraph
open LatticeProb.Network.DirichletExamples

attribute [local instance] pathLocallyFinite

/-- The affine path potential is harmonic at every vertex other than the two terminals. -/
theorem pathHalf_harmonic_off_terminals :
    ∀ x : Fin 3, x ≠ 0 → x ≠ 2 →
      netLaplacian (pathGraph 3) (unitCond (pathGraph 3)) pathHalf x = 0 := by
  intro x hx0 hx2
  have hx : x = 1 := by fin_cases x <;> simp_all
  rw [hx]
  exact pathHalf_harmonic_one

/-- The affine path potential has prescribed boundary values zero and one. -/
theorem pathHalf_terminal_values : pathHalf 0 = 0 ∧ pathHalf 2 = 1 := by
  norm_num [pathHalf]

/-- The affine potential is nonconstant on the actual three-vertex path. -/
theorem pathHalf_nonconstant : ∃ x y : Fin 3, pathHalf x ≠ pathHalf y := by
  refine ⟨0, 2, ?_⟩
  rw [pathHalf_terminal_values.1, pathHalf_terminal_values.2]
  norm_num

/-- Terminal separation applies to the actual affine path potential with an interior vertex. -/
theorem pathHalf_terminal_ne : pathHalf 0 ≠ pathHalf 2 := by
  exact terminal_ne_of_harmonic_off_terminals
    (show (pathGraph 3).Connected from pathGraph_connected 2) isCond_unitCond
    pathHalf_harmonic_off_terminals pathHalf_nonconstant

/-- Any potential on the path with these harmonicity and boundary data is the affine one
on all three vertices. -/
theorem eq_pathHalf_of_boundary {u : Fin 3 → ℝ}
    (hu : ∀ x, x ≠ 0 → x ≠ 2 →
      netLaplacian (pathGraph 3) (unitCond (pathGraph 3)) u x = 0)
    (hu0 : u 0 = 0) (hu2 : u 2 = 1) : u = pathHalf := by
  apply eq_of_harmonic_off_boundary
    (show (pathGraph 3).Connected from pathGraph_connected 2) isCond_unitCond
    (B := {0, 2}) ⟨0, Set.mem_insert 0 {2}⟩
  · intro x hx
    have hx0 : x ≠ 0 := fun h => hx (by simp only [h, Set.mem_insert_iff,
      Set.mem_singleton_iff, true_or])
    have hx2 : x ≠ 2 := fun h => hx (by simp only [h, Set.mem_insert_iff,
      Set.mem_singleton_iff, or_true])
    exact hu x hx0 hx2
  · intro x hx
    have hx0 : x ≠ 0 := fun h => hx (by simp only [h, Set.mem_insert_iff,
      Set.mem_singleton_iff, true_or])
    have hx2 : x ≠ 2 := fun h => hx (by simp only [h, Set.mem_insert_iff,
      Set.mem_singleton_iff, or_true])
    exact pathHalf_harmonic_off_terminals x hx0 hx2
  · intro x hx
    rcases hx with rfl | hx
    · exact hu0.trans pathHalf_terminal_values.1.symm
    · rw [Set.mem_singleton_iff.mp hx]
      exact hu2.trans pathHalf_terminal_values.2.symm

end LatticeProb.Network.FiniteBoundaryConsumers
