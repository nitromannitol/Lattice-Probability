import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential

/-! # Exponential decay and inverse powers -/

set_option autoImplicit false

namespace LatticeProb

/-- An exponential of an inverse power is bounded by every corresponding
integer power, with an explicit constant. -/
theorem exp_neg_inv_rpow_le {c x a : ℝ} (hc : 0 < c) (hx : 0 < x) (n : ℕ) :
    Real.exp (-(c * x ^ (-a))) ≤ (n.factorial : ℝ) / c ^ n * x ^ (a * n) := by
  let y : ℝ := c * x ^ (-a)
  have hy : 0 < y := by dsimp [y]; positivity
  have hfact : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hseries : y ^ n ≤ (n.factorial : ℝ) * Real.exp y := by
    simpa only [mul_comm] using
      (div_le_iff₀ hfact).mp (Real.pow_div_factorial_le_exp y hy.le n)
  have hbound : y ^ n * Real.exp (-y) ≤ (n.factorial : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hseries (Real.exp_nonneg (-y))
    have he : Real.exp y * Real.exp (-y) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith [he]
  have hpow : y ^ n = c ^ n / x ^ (a * n) := by
    dsimp [y]
    rw [mul_pow, ← Real.rpow_natCast (x ^ (-a)) n, ← Real.rpow_mul hx.le]
    rw [show -a * (n : ℝ) = -(a * n) by ring, Real.rpow_neg hx.le]
    ring
  have hxpow : 0 < x ^ (a * n) := Real.rpow_pos_of_pos hx _
  rw [hpow] at hbound
  have hcpos : 0 < c ^ n := pow_pos hc n
  change Real.exp (-y) ≤ (n.factorial : ℝ) / c ^ n * x ^ (a * n)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hcpos).2
  rw [div_mul_eq_mul_div] at hbound
  have h := (div_le_iff₀ hxpow).mp hbound
  nlinarith

end LatticeProb
