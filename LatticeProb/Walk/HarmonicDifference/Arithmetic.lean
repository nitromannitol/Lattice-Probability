import Mathlib

/-!
# Radius bounds for the pair-chain barrier

The half-radius and the scaling of the quadratic barrier yield the numerical
constant in the harmonic difference estimate.
-/

namespace LatticeProb.HarmonicDifference

/-- Elementary bounds for the half-radius. -/
theorem half_radius_bounds (n : ℕ) (hn : 4 ≤ n) :
    0 < (n + 1) / 2 ∧ n ≤ 2 * ((n + 1) / 2) ∧
      2 * (((n + 1) / 2) - 1) ≤ n ∧ 2 * ((n + 1) / 2) ≤ n + 1 := by
  omega

/-- The quadratic scaling is normalized at three quarters of the radius. -/
theorem barrier_scale_identity (n : ℝ) (hn : n ≠ 0) :
    (16 / (9 * n ^ 2)) * (3 * n / 4) ^ 2 = 1 := by
  field_simp
  ring

/-- The numerical bound for the barrier at unit separation. -/
theorem barrier_initial_numeric (n L d M : ℝ) (hn : 4 ≤ n) (hL : 0 < L)
    (hlo : n ≤ 2 * L) (hhi : 2 * L - 1 ≤ n) (hd : 0 ≤ d) (hM : 0 ≤ M) :
    2 * M * (1 / L + (16 / (9 * n ^ 2)) * (1 / 4 + d / 2 * (2 * L - 1))) ≤
      (2 * d + 6) * M / n := by
  have hnpos : 0 < n := by linarith
  have hlin : 1 / L ≤ 2 / n := by
    apply (div_le_div_iff₀ hL hnpos).2
    nlinarith
  have hquad : 1 / 4 + d / 2 * (2 * L - 1) ≤ 1 / 4 + d / 2 * n := by
    nlinarith [mul_nonneg hd (show 0 ≤ n - (2 * L - 1) by linarith)]
  have hcoef : 0 ≤ 16 / (9 * n ^ 2) := by positivity
  have hquad' : (16 / (9 * n ^ 2)) * (1 / 4 + d / 2 * (2 * L - 1)) ≤
      (16 / (9 * n ^ 2)) * (1 / 4 + d / 2 * n) :=
    mul_le_mul_of_nonneg_left hquad hcoef
  have hestimate : (16 / (9 * n ^ 2)) * (1 / 4 + d / 2 * n) ≤
      (1 / 9 + 8 * d / 9) / n := by
    have hnsq : 0 < 9 * n ^ 2 := by positivity
    apply (le_div_iff₀ hnpos).2
    field_simp
    nlinarith [mul_nonneg hd (show 0 ≤ n - 4 by linarith)]
  have hfinal : 2 * (2 / n + (1 / 9 + 8 * d / 9) / n) ≤ (2 * d + 6) / n := by
    apply (le_div_iff₀ hnpos).2
    field_simp
    nlinarith
  have hmain : 2 * (1 / L + (16 / (9 * n ^ 2)) * (1 / 4 + d / 2 * (2 * L - 1))) ≤
      (2 * d + 6) / n := by linarith
  have := mul_le_mul_of_nonneg_left hmain hM
  convert this using 1 <;> ring

end LatticeProb.HarmonicDifference
