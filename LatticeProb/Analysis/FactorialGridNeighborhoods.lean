import LatticeProb.Analysis.FactorialMesh

/-!
# Factorial grid neighborhoods

Closed squares around a factorial grid have uniformly vanishing diameter.
Coordinatewise proximity to a grid point implies membership in its square.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology ENNReal

namespace LatticeProb

/-- The reciprocal mesh of the sixth-power factorial grid. -/
noncomputable def factorialGridMesh (n : ℕ) : ℝ :=
  1 / ((n.factorial ^ 6 : ℕ) : ℝ)

/-- A closed square centered at a pair of factorial grid points. -/
def factorialGridNeighborhood (n : ℕ)
    (i j : Fin (n.factorial ^ 6)) : Set (ℝ × ℝ) :=
  Metric.closedBall
    ((i.val : ℝ) / (n.factorial ^ 6 : ℕ),
      (j.val : ℝ) / (n.factorial ^ 6 : ℕ)) (factorialGridMesh n)

/-- Coordinatewise mesh proximity gives membership in the corresponding square. -/
theorem mem_factorialGridNeighborhood (n : ℕ)
    (i j : Fin (n.factorial ^ 6)) (a s : ℝ)
    (ha : |a - (i.val : ℝ) / (n.factorial ^ 6 : ℕ)| ≤ factorialGridMesh n)
    (hs : |s - (j.val : ℝ) / (n.factorial ^ 6 : ℕ)| ≤ factorialGridMesh n) :
    (a, s) ∈ factorialGridNeighborhood n i j := by
  simpa only [factorialGridNeighborhood, Metric.mem_closedBall, Prod.dist_eq,
    Real.dist_eq, max_le_iff] using And.intro ha hs

/-- The extended diameter is bounded uniformly by twice the grid mesh. -/
theorem ediam_factorialGridNeighborhood_le (n : ℕ)
    (i j : Fin (n.factorial ^ 6)) :
    Metric.ediam (factorialGridNeighborhood n i j) ≤
      ENNReal.ofReal (2 * factorialGridMesh n) := by
  apply Metric.ediam_le_of_forall_dist_le
  intro x hx y hy
  have hx' := Metric.mem_closedBall.mp hx
  have hy' := Metric.mem_closedBall.mp hy
  have h := dist_triangle x
    ((i.val : ℝ) / (n.factorial ^ 6 : ℕ),
      (j.val : ℝ) / (n.factorial ^ 6 : ℕ)) y
  have hy'' : dist ((i.val : ℝ) / (n.factorial ^ 6 : ℕ),
      (j.val : ℝ) / (n.factorial ^ 6 : ℕ)) y ≤ factorialGridMesh n := by
    simpa only [dist_comm] using hy'
  linarith

/-- The uniform extended-diameter bound tends to zero. -/
theorem tendsto_factorialGridNeighborhood_diameter :
    Tendsto (fun n : ℕ => ENNReal.ofReal (2 * factorialGridMesh n)) atTop (𝓝 0) := by
  have hmesh : Tendsto factorialGridMesh atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => 1 / ((n.factorial ^ 6 : ℕ) : ℝ)) atTop (𝓝 0)
    simpa only [Nat.cast_pow] using
      tendsto_one_div_factorial_pow 6 (by norm_num)
  simpa only [mul_zero, ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal (hmesh.const_mul 2)

end LatticeProb
