import Mathlib

/-!
# Power decay for two-dimensional grid costs

A positive mesh with sufficient exponent slack makes the product of the
number of grid pairs, a diameter power, and a survival power tend to zero.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace LatticeProb

/-- The exponent of the grid-cost product is the sum of its contributions. -/
theorem grid_power_cost_eq (x α β p : ℝ) (hx : 0 < x) :
    x⁻¹ ^ 2 * x ^ β * (x ^ α) ^ (p + 2) =
      x ^ (β + α * (p + 2) - 2) := by
  rw [Real.rpow_sub hx, Real.rpow_add hx, Real.rpow_mul hx.le]
  simp only [Real.rpow_two, div_eq_mul_inv, inv_pow]
  ring

/-- The grid-cost product tends to zero when its combined exponent is positive. -/
theorem tendsto_grid_power_cost {x : ℕ → ℝ} (hx : ∀ n, 0 < x n)
    (hlim : Tendsto x atTop (𝓝 0)) (α β p : ℝ)
    (hslack : 2 < β + α * (p + 2)) :
    Tendsto (fun n => (x n)⁻¹ ^ 2 * (x n) ^ β * ((x n) ^ α) ^ (p + 2))
      atTop (𝓝 0) := by
  have hp : 0 < β + α * (p + 2) - 2 := by linarith
  have h := (Real.continuousAt_rpow_const 0 _ (Or.inr hp.le)).tendsto.comp hlim
  simp only [Real.zero_rpow (ne_of_gt hp)] at h
  exact h.congr fun n => (grid_power_cost_eq (x n) α β p (hx n)).symm

end LatticeProb
