import LatticeProb.Graph.Zd.IntegerLaplacian

/-!
# A nonzero delta function consuming lattice integrality

The delta at the origin has singleton support and an integer full lattice Laplacian,
as follows by casting the corresponding finite integer sum. The integrality theorem
therefore applies nonvacuously in dimensions two and one.
-/

namespace LatticeProb.Graph.Zd

open LatticeProb Percolation

/-- The real delta function at the origin of the integer lattice. -/
noncomputable def originDelta (d : ℕ) (x : Fin d → ℤ) : ℝ :=
  if x = 0 then 1 else 0

/-- The delta has finite support, takes value one at the origin, and has integer Laplacian. -/
theorem originDelta_data (d : ℕ) :
    (Function.support (originDelta d)).Finite ∧ originDelta d 0 = 1 ∧
      ∀ x, ∃ n : ℤ, laplacian (nearestNeighborGraph d) (originDelta d) x = (n : ℝ) := by
  classical
  refine ⟨(Set.finite_singleton (0 : Fin d → ℤ)).subset ?_, ?_, ?_⟩
  · intro x hx
    by_contra h
    exact hx (if_neg (show x ≠ 0 from h))
  · exact if_pos rfl
  · intro x
    refine ⟨∑ y ∈ (nearestNeighborGraph d).neighborFinset x,
      ((if y = 0 then 1 else 0 : ℤ) - (if x = 0 then 1 else 0 : ℤ)), ?_⟩
    rw [laplacian, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro y _
    simp only [Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero, originDelta]

/-- The positive-dimensional theorem applies to a nonzero delta on the full square lattice. -/
theorem integer_delta_consumer :
    originDelta 2 0 = 1 ∧
      (∀ x, ∃ n : ℤ, laplacian (nearestNeighborGraph 2) (originDelta 2) x = (n : ℝ)) ∧
      (∀ x, ∃ n : ℤ, originDelta 2 x = (n : ℝ)) := by
  obtain ⟨hs, hzero, hΔ⟩ := originDelta_data 2
  exact ⟨hzero, hΔ, integer_values_of_finite_support_integer_laplacian
    (by decide) (originDelta 2) hs hΔ⟩

/-- The stronger library result also applies in dimension one. -/
theorem integer_delta_one_dimensional_consumer :
    ∀ x, ∃ n : ℤ, originDelta 1 x = (n : ℝ) :=
  integer_values_of_finite_support_integer_laplacian (by decide) (originDelta 1)
    (originDelta_data 1).1 (originDelta_data 1).2.2

end LatticeProb.Graph.Zd
