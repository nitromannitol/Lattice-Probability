module

/-
Polynomially weighted summability of stretched-exponential sequences.

For `c > 0` and `r : ℕ`, the sequence `s ↦ s ^ r · exp(-c √s)` is summable over `s : ℕ`.
The proof compares it with `(k! / c ^ k) · s⁻²` for `k = 2r + 4`, using `x ^ k / k! ≤ exp x`
at `x = c √s`.

These are analytic bounds for real sequences.
-/
public import Mathlib

@[expose] public section

namespace LatticeProb

/-- For `c > 0`, `x ≥ 0`, and every `k : ℕ`, `x ^ k · exp(-c x) ≤ k! / c ^ k`. -/
theorem pow_mul_exp_neg_mul_le_factorial_div (c x : ℝ) (hc : 0 < c) (hx : 0 ≤ x) (k : ℕ) :
    x ^ k * Real.exp (-(c * x)) ≤ (Nat.factorial k : ℝ) / c ^ k := by
  have hE : 0 < Real.exp (c * x) := Real.exp_pos _
  have h1 : (c * x) ^ k / (Nat.factorial k : ℝ) ≤ Real.exp (c * x) :=
    Real.pow_div_factorial_le_exp (c * x) (mul_nonneg hc.le hx) k
  have hfac : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h2 : (c * x) ^ k ≤ Real.exp (c * x) * (Nat.factorial k : ℝ) :=
    (div_le_iff₀ hfac).1 h1
  have hck : (0 : ℝ) < c ^ k := pow_pos hc k
  rw [mul_pow] at h2
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hE hck]
  calc x ^ k * c ^ k = c ^ k * x ^ k := mul_comm _ _
    _ ≤ Real.exp (c * x) * (Nat.factorial k : ℝ) := h2
    _ = (Nat.factorial k : ℝ) * Real.exp (c * x) := mul_comm _ _

/-- For `c > 0`, `s ≥ 1`, and `r : ℕ`, `s ^ r · exp(-c √s) ≤ (k! / c ^ k) · (1 / s ^ 2)`
with `k = 2r + 4`. -/
theorem pow_mul_exp_neg_sqrt_le_factorial_div_mul_inv_sq (c : ℝ) (hc : 0 < c) (r s : ℕ)
    (hs : 1 ≤ s) :
    (s : ℝ) ^ r * Real.exp (-c * Real.sqrt (s : ℝ)) ≤
      ((Nat.factorial (2 * r + 4) : ℝ) / c ^ (2 * r + 4)) * (1 / (s : ℝ) ^ 2) := by
  have hs0 : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr (by omega)
  have hs2 : (0 : ℝ) < (s : ℝ) ^ 2 := pow_pos hs0 2
  have hx : Real.sqrt (s : ℝ) ^ 2 = (s : ℝ) := Real.sq_sqrt (Nat.cast_nonneg s)
  have hpow : Real.sqrt (s : ℝ) ^ (2 * r + 4) = (s : ℝ) ^ r * (s : ℝ) ^ 2 := by
    have h := (by ring : Real.sqrt (s : ℝ) ^ (2 * r + 4) =
      (Real.sqrt (s : ℝ) ^ 2) ^ r * (Real.sqrt (s : ℝ) ^ 2) ^ 2)
    rw [hx] at h
    exact h
  have hk := pow_mul_exp_neg_mul_le_factorial_div c (Real.sqrt (s : ℝ)) hc (Real.sqrt_nonneg _)
    (2 * r + 4)
  rw [hpow] at hk
  rw [neg_mul, mul_one_div, le_div_iff₀ hs2]
  calc (s : ℝ) ^ r * Real.exp (-(c * Real.sqrt (s : ℝ))) * (s : ℝ) ^ 2
      = (s : ℝ) ^ r * (s : ℝ) ^ 2 * Real.exp (-(c * Real.sqrt (s : ℝ))) :=
        mul_right_comm _ _ _
    _ ≤ (Nat.factorial (2 * r + 4) : ℝ) / c ^ (2 * r + 4) := hk

/-- For `c > 0` and `r : ℕ`, the weight `s ↦ s ^ r · exp(-c √s)` is summable over
`s : ℕ`. -/
theorem summable_pow_mul_exp_neg_sqrt (c : ℝ) (hc : 0 < c) (r : ℕ) :
    Summable (fun s : ℕ => (s : ℝ) ^ r * Real.exp (-c * Real.sqrt (s : ℝ))) := by
  refine Summable.of_norm_bounded_eventually
    (g := fun s : ℕ =>
      ((Nat.factorial (2 * r + 4) : ℝ) / c ^ (2 * r + 4)) * (1 / (s : ℝ) ^ 2))
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _) ?_
  rw [Nat.cofinite_eq_atTop]
  refine Filter.eventually_atTop.2 ⟨1, fun s hs => ?_⟩
  show ‖(s : ℝ) ^ r * Real.exp (-c * Real.sqrt (s : ℝ))‖ ≤
    ((Nat.factorial (2 * r + 4) : ℝ) / c ^ (2 * r + 4)) * (1 / (s : ℝ) ^ 2)
  have hnn : (0 : ℝ) ≤ (s : ℝ) ^ r * Real.exp (-c * Real.sqrt (s : ℝ)) := by positivity
  rw [Real.norm_of_nonneg hnn]
  exact pow_mul_exp_neg_sqrt_le_factorial_div_mul_inv_sq c hc r s hs

end LatticeProb
