/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistGeometricBudget at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistPointFieldFactor

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_geometric_range_le (q : ℝ) (hq0 : 0 ≤ q)
    (hq1 : q < 1) (N : ℕ) :
    ∑ j ∈ Finset.range N, q ^ j ≤ 1 / (1 - q) := by
  simpa only [Nat.Ico_zero_eq_range, pow_zero] using
    (geom_sum_Ico_le_of_lt_one (m := 0) (n := N) hq0 hq1)

theorem pt_dist_geometric_arm_le (q : ℝ) (hq0 : 0 ≤ q)
    (hq1 : q < 1) (k₀ N : ℕ) :
    ∑ j ∈ Finset.range N,
      (q ^ (k₀ + (j + 1)) + q ^ (k₀ + (j + 1)) +
        q ^ (k₀ + j)) ≤
      3 * q ^ k₀ / (1 - q) := by
  have hterm (j : ℕ) :
      q ^ (k₀ + (j + 1)) + q ^ (k₀ + (j + 1)) +
        q ^ (k₀ + j) ≤ 3 * q ^ k₀ * q ^ j := by
    simp only [pow_add, pow_succ]
    have hqj : 0 ≤ q ^ j := pow_nonneg hq0 _
    have hqk : 0 ≤ q ^ k₀ := pow_nonneg hq0 _
    have hq : q ≤ 1 := hq1.le
    have hqmul : q ^ k₀ * q ^ j * q ≤ q ^ k₀ * q ^ j := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hq (mul_nonneg hqk hqj))
    nlinarith
  calc
    _ ≤ ∑ j ∈ Finset.range N, 3 * q ^ k₀ * q ^ j :=
      Finset.sum_le_sum fun j _ => hterm j
    _ = 3 * q ^ k₀ * (∑ j ∈ Finset.range N, q ^ j) := by
      rw [Finset.mul_sum]
    _ ≤ 3 * q ^ k₀ * (1 / (1 - q)) :=
      mul_le_mul_of_nonneg_left
        (pt_dist_geometric_range_le q hq0 hq1 N) (by positivity)
    _ = _ := by ring

end SupercriticalLQGUniqueness.B2.DG20Pt
