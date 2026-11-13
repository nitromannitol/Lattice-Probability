import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exponents of comparable power functions

If two power functions `r ↦ r ^ a` and `r ↦ r ^ b` are comparable up to a multiplicative constant on
`(0, ∞)`, that is `C⁻¹ r ^ a ≤ r ^ b ≤ C r ^ a` for every `r > 0`, then `a = b`. This is how a scaling
constant `c_r` comparable to both `r ^ a` and `r ^ b` (for instance the scaling constants of a weak
LQG metric) determines its exponent.

* `eq_of_rpow_le_mul_rpow`: the statement above, with one constant for both bounds;
* `eq_of_rpow_comparable`: the same for a positive function `c` comparable to both power functions.
-/

set_option autoImplicit false

open Real

namespace LatticeProb.Analysis

/-- **Comparable power functions have equal exponents.** If `C⁻¹ r ^ a ≤ r ^ b ≤ C r ^ a` for every
`r > 0`, then `a = b`. -/
theorem eq_of_rpow_le_mul_rpow {a b C : ℝ} (hC : 0 < C)
    (h : ∀ r : ℝ, 0 < r → C⁻¹ * r ^ a ≤ r ^ b ∧ r ^ b ≤ C * r ^ a) : a = b := by
  -- with `r = exp t`: `|(b - a) t| ≤ log C` for every real `t`
  have key : ∀ t : ℝ, (b - a) * t ≤ Real.log C ∧ (a - b) * t ≤ Real.log C := by
    intro t
    obtain ⟨h₁, h₂⟩ := h (Real.exp t) (Real.exp_pos t)
    rw [← Real.exp_mul, ← Real.exp_mul] at h₁ h₂
    have hCe : C = Real.exp (Real.log C) := (Real.exp_log hC).symm
    constructor
    · have : Real.exp (t * b) ≤ Real.exp (Real.log C) * Real.exp (t * a) := by rwa [← hCe]
      rw [← Real.exp_add, Real.exp_le_exp] at this
      linarith
    · have : Real.exp (-Real.log C) * Real.exp (t * a) ≤ Real.exp (t * b) := by
        rwa [Real.exp_neg, ← hCe]
      rw [← Real.exp_add, Real.exp_le_exp] at this
      linarith
  by_contra hne
  have hd : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  set t := (|Real.log C| + 1) / (b - a) with ht
  have h1 : (b - a) * t = |Real.log C| + 1 := by
    rw [ht]; field_simp
  have := (key t).1
  rw [h1] at this
  linarith [le_abs_self (Real.log C)]

/-- **A function comparable to two power functions determines the exponent.** If `c > 0` on `(0, ∞)`
and `c r` is comparable to both `r ^ a` and `r ^ b` up to multiplicative constants, then `a = b`. -/
theorem eq_of_rpow_comparable {a b C₁ C₂ : ℝ} {c : ℝ → ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (ha : ∀ r : ℝ, 0 < r → C₁⁻¹ * r ^ a ≤ c r ∧ c r ≤ C₁ * r ^ a)
    (hb : ∀ r : ℝ, 0 < r → C₂⁻¹ * r ^ b ≤ c r ∧ c r ≤ C₂ * r ^ b) : a = b := by
  refine eq_of_rpow_le_mul_rpow (mul_pos hC₁ hC₂) fun r hr => ?_
  obtain ⟨ha₁, ha₂⟩ := ha r hr
  obtain ⟨hb₁, hb₂⟩ := hb r hr
  have hra : 0 < r ^ a := Real.rpow_pos_of_pos hr a
  have hrb : 0 < r ^ b := Real.rpow_pos_of_pos hr b
  constructor
  · -- `(C₁ C₂)⁻¹ r^a ≤ C₂⁻¹ c r ≤ r^b`
    have e1 : (C₁ * C₂)⁻¹ * r ^ a = C₂⁻¹ * (C₁⁻¹ * r ^ a) := by
      rw [mul_inv]; ring
    rw [e1]
    calc C₂⁻¹ * (C₁⁻¹ * r ^ a) ≤ C₂⁻¹ * c r :=
          mul_le_mul_of_nonneg_left ha₁ (inv_nonneg.2 hC₂.le)
      _ ≤ C₂⁻¹ * (C₂ * r ^ b) := mul_le_mul_of_nonneg_left hb₂ (inv_nonneg.2 hC₂.le)
      _ = r ^ b := by field_simp
  · calc r ^ b = C₂ * (C₂⁻¹ * r ^ b) := by field_simp
      _ ≤ C₂ * c r := mul_le_mul_of_nonneg_left hb₁ hC₂.le
      _ ≤ C₂ * (C₁ * r ^ a) := mul_le_mul_of_nonneg_left ha₂ hC₂.le
      _ = C₁ * C₂ * r ^ a := by ring

end LatticeProb.Analysis
