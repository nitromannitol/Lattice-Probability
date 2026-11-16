import Mathlib.Basic.ENNReal.Real
import Mathlib.Tactic

/-! # Extended nonnegative real finite-horizon estimates -/

set_option autoImplicit false

open scoped NNReal ENNReal

namespace LatticeProb

/-- A nonnegative real finite-horizon budget bounds its extended-real form. -/
theorem ennreal_finite_horizon_budget {L : ℕ} {b τ : ℝ} {r : ℝ≥0}
    (hb : 0 ≤ b) (hτ : 0 ≤ τ)
    (hbudget : 2 * (L + 1 : ℝ) * b + 3 * τ ≤ (r : ℝ)) :
    ((L + 1 : ℝ≥0∞) * ENNReal.ofReal b +
      (ENNReal.ofReal τ + ENNReal.ofReal τ)) +
      (ENNReal.ofReal τ + (L + 1 : ℝ≥0∞) * ENNReal.ofReal b) ≤ (r : ℝ≥0∞) := by
  have hnat : ENNReal.ofReal (L + 1 : ℝ) = (L + 1 : ℝ≥0∞) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (ENNReal.ofReal_natCast (L + 1))
  have hprod : ENNReal.ofReal ((L + 1 : ℝ) * b) =
      (L + 1 : ℝ≥0∞) * ENNReal.ofReal b := by
    rw [ENNReal.ofReal_mul (by positivity), hnat]
  have hnonneg : 0 ≤ (L + 1 : ℝ) * b := mul_nonneg (by positivity) hb
  have heq : ENNReal.ofReal (2 * (L + 1 : ℝ) * b + 3 * τ) =
      ((L + 1 : ℝ≥0∞) * ENNReal.ofReal b +
        (ENNReal.ofReal τ + ENNReal.ofReal τ)) +
        (ENNReal.ofReal τ + (L + 1 : ℝ≥0∞) * ENNReal.ofReal b) := by
    have hid : 2 * (L + 1 : ℝ) * b + 3 * τ =
        (((L + 1 : ℝ) * b + (τ + τ)) + (τ + (L + 1 : ℝ) * b)) := by ring
    rw [hid, ENNReal.ofReal_add (add_nonneg hnonneg (add_nonneg hτ hτ))
      (add_nonneg hτ hnonneg), ENNReal.ofReal_add hnonneg (add_nonneg hτ hτ),
      ENNReal.ofReal_add hτ hτ, ENNReal.ofReal_add hτ hnonneg, hprod]
  rw [← heq, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hbudget

/-- Strict real bounds below a positive radius give strict extended-real bounds. -/
theorem ennreal_lt_coe_of_lt {x : ℝ} {r : ℝ≥0} (hr : 0 < r)
    (h : x < (r : ℝ)) : ENNReal.ofReal x < (r : ℝ≥0∞) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  exact (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hr)).2 h

end LatticeProb
