import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Power bounds for a normalized intermediate radius -/

set_option autoImplicit false

namespace LatticeProb

/-- Choosing the intermediate radius `d ^ a / 2` makes both terms in a
polynomial exit estimate decay at least as fast as `d ^ q`. -/
theorem intermediate_radius_power_bounds {d a p q : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (n : ℕ) (hq1 : q ≤ (1 - a) * p) (hq2 : q ≤ 2 * a * n) :
    (d / (d ^ a / 2)) ^ p ≤ (2 : ℝ) ^ p * d ^ q ∧
      (4 * (d ^ a / 2) ^ 2) ^ n ≤ d ^ q := by
  have hda : 0 < d ^ a := Real.rpow_pos_of_pos hd _
  have hratio : d / (d ^ a / 2) = 2 * d ^ (1 - a) := by
    rw [Real.rpow_sub hd, Real.rpow_one]
    field_simp
  constructor
  · rw [hratio, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hd.le _),
      ← Real.rpow_mul hd.le]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 hq1) (Real.rpow_nonneg (by norm_num) _)
  · have heq : 4 * (d ^ a / 2) ^ 2 = d ^ (2 * a) := by
      rw [show 2 * a = a * (2 : ℝ) by ring, Real.rpow_mul hd.le]
      norm_num [Real.rpow_natCast]; ring
    rw [heq, ← Real.rpow_natCast, ← Real.rpow_mul hd.le]
    exact Real.rpow_le_rpow_of_exponent_ge hd hd1 hq2

end LatticeProb
