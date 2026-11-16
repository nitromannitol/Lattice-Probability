import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Polynomials against Gaussian and singular exponential factors

Elementary uniform bounds that absorb a power into an exponential.  They rest on the estimate
`x^n ≤ n! exp x` for `x ≥ 0`, which is the `n`-th term of the exponential series.

* A polynomial in `s ≥ 0` is bounded against the Gaussian weight `exp(-s²/8)`: the product
  `(1 + s)^n (1 + s²)^k exp(-s²/8)` is bounded by a constant depending only on `n` and `k`.
* For `c > 0` the singular powers `(1/t)^m` and `(1/√t)^m` are bounded against the vanishing
  factor `exp(-c/t)` uniformly in `t > 0`.

These are the scalar inequalities behind the uniform control of every derivative of the heat
kernel away from the singularity at time zero.
-/

namespace LatticeProb.Analysis.Schauder

open Real

noncomputable section

/-- The `n`-th term of the exponential series: `x^n ≤ n! exp x` for `x ≥ 0`. -/
private theorem pow_le_factorial_mul_exp {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ n ≤ (Nat.factorial n : ℝ) * Real.exp x := by
  have h := Real.pow_div_factorial_le_exp x hx n
  have hf : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf] at h
  linarith

/-- For any real `z` the elementary bound `z ≤ 1 + z²`. -/
private theorem self_le_one_add_sq (z : ℝ) : z ≤ 1 + z ^ 2 := by
  nlinarith [sq_nonneg (z - 1), sq_nonneg z]

/-- A power is dominated by one plus the power of twice the exponent: `s^N ≤ 1 + s^(2N)`. -/
private theorem pow_le_one_add_pow_two_mul (s : ℝ) (N : ℕ) : s ^ N ≤ 1 + s ^ (2 * N) := by
  have h := self_le_one_add_sq (s ^ N)
  rwa [← pow_mul'] at h

/-- A polynomial in `s ≥ 0` times `exp(-s²/8)` is bounded. -/
theorem exists_one_add_pow_mul_exp_le (n k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s →
      (1 + s) ^ n * (1 + s ^ 2) ^ k * Real.exp (-(s ^ 2) / 8) ≤ C := by
  refine ⟨2 ^ (n + 2 * k) * (2 + 8 ^ (n + 2 * k) * (Nat.factorial (n + 2 * k) : ℝ)),
    by positivity, fun s hs => ?_⟩
  generalize hN : n + 2 * k = N
  have hE0 : 0 ≤ Real.exp (-(s ^ 2) / 8) := (Real.exp_pos _).le
  have hE1 : Real.exp (-(s ^ 2) / 8) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ s ^ 2 := sq_nonneg s
    linarith
  have hEF : Real.exp (-(s ^ 2) / 8) * Real.exp (s ^ 2 / 8) = 1 := by
    rw [← Real.exp_add]
    have : -(s ^ 2) / 8 + s ^ 2 / 8 = 0 := by ring
    rw [this, Real.exp_zero]
  have h1 : (1 + s) ^ n * (1 + s ^ 2) ^ k ≤ (1 + s) ^ N := by
    have h : (1 + s ^ 2) ^ k ≤ ((1 + s) ^ 2) ^ k :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) k
    calc (1 + s) ^ n * (1 + s ^ 2) ^ k ≤ (1 + s) ^ n * ((1 + s) ^ 2) ^ k := by gcongr
      _ = (1 + s) ^ N := by rw [← pow_mul, ← pow_add, ← hN]
  have h2 : (1 + s) ^ N ≤ 2 ^ N * (1 + s ^ N) := by
    rcases le_total s 1 with h | h
    · have h3 : (1 + s) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      have h4 : 0 ≤ s ^ N := by positivity
      have h5 : (0 : ℝ) ≤ 2 ^ N := by positivity
      nlinarith
    · have h3 : (1 + s) ^ N ≤ (2 * s) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      rw [mul_pow] at h3
      have h4 : 0 ≤ s ^ N := by positivity
      have h5 : (0 : ℝ) ≤ 2 ^ N := by positivity
      nlinarith
  have h3 : s ^ N ≤ 1 + 8 ^ N * (Nat.factorial N : ℝ) * Real.exp (s ^ 2 / 8) := by
    have h4 : s ^ (2 * N) = 8 ^ N * (s ^ 2 / 8) ^ N := by
      rw [pow_mul, ← mul_pow]
      congr 1
      ring
    have h5 := pow_le_factorial_mul_exp (x := s ^ 2 / 8) (by positivity) N
    have h6 : (0 : ℝ) ≤ 8 ^ N := by positivity
    have h7 := mul_le_mul_of_nonneg_left h5 h6
    have h8 := pow_le_one_add_pow_two_mul s N
    rw [h4] at h8
    nlinarith
  have key : (1 + s) ^ N * Real.exp (-(s ^ 2) / 8) ≤
      2 ^ N * (2 + 8 ^ N * (Nat.factorial N : ℝ)) := by
    have h5 : (0 : ℝ) ≤ 2 ^ N := by positivity
    calc (1 + s) ^ N * Real.exp (-(s ^ 2) / 8)
        ≤ (2 ^ N * (1 + s ^ N)) * Real.exp (-(s ^ 2) / 8) := by gcongr
      _ ≤ (2 ^ N * (2 + 8 ^ N * (Nat.factorial N : ℝ) * Real.exp (s ^ 2 / 8))) *
          Real.exp (-(s ^ 2) / 8) := by
        have h6 : 1 + s ^ N ≤ 2 + 8 ^ N * (Nat.factorial N : ℝ) * Real.exp (s ^ 2 / 8) := by
          linarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h6 h5) hE0
      _ = 2 ^ N * (2 * Real.exp (-(s ^ 2) / 8) + 8 ^ N * (Nat.factorial N : ℝ) *
          (Real.exp (-(s ^ 2) / 8) * Real.exp (s ^ 2 / 8))) := by ring
      _ = 2 ^ N * (2 * Real.exp (-(s ^ 2) / 8) + 8 ^ N * (Nat.factorial N : ℝ)) := by
        rw [hEF, mul_one]
      _ ≤ 2 ^ N * (2 + 8 ^ N * (Nat.factorial N : ℝ)) := by
        gcongr
        linarith
  calc (1 + s) ^ n * (1 + s ^ 2) ^ k * Real.exp (-(s ^ 2) / 8)
      ≤ (1 + s) ^ N * Real.exp (-(s ^ 2) / 8) := by gcongr
    _ ≤ 2 ^ N * (2 + 8 ^ N * (Nat.factorial N : ℝ)) := key

/-- A power of `1/t` times `exp(-c/t)` is bounded on `t > 0`. -/
theorem exists_inv_pow_mul_exp_le (m : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → (1 / t) ^ m * Real.exp (-(c / t)) ≤ C := by
  refine ⟨(Nat.factorial m : ℝ) / c ^ m, by positivity, fun t ht => ?_⟩
  have hu : 0 ≤ c / t := by positivity
  have h1 : (1 / t) ^ m = (c / t) ^ m / c ^ m := by
    rw [← div_pow]
    congr 1
    field_simp
  have h2 := pow_le_factorial_mul_exp hu m
  have hEF : Real.exp (-(c / t)) * Real.exp (c / t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hcm : 0 < c ^ m := pow_pos hc m
  calc (1 / t) ^ m * Real.exp (-(c / t))
      = (c / t) ^ m * Real.exp (-(c / t)) / c ^ m := by rw [h1]; ring
    _ ≤ (Nat.factorial m : ℝ) * Real.exp (c / t) * Real.exp (-(c / t)) / c ^ m := by
      gcongr
    _ = (Nat.factorial m : ℝ) / c ^ m := by
      rw [mul_assoc, mul_comm (Real.exp (c / t)), hEF, mul_one]

/-- The same with a half-integer power: `(1/√t)^m exp(-c/t)` is bounded on `t > 0`. -/
theorem exists_inv_sqrt_pow_mul_exp_le (m : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, 0 < t → (1 / Real.sqrt t) ^ m * Real.exp (-(c / t)) ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_inv_pow_mul_exp_le m hc
  refine ⟨1 + C, by linarith, fun t ht => ?_⟩
  have hE0 : 0 ≤ Real.exp (-(c / t)) := (Real.exp_pos _).le
  have hE1 : Real.exp (-(c / t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ c / t := by positivity
    linarith
  have hsq : (1 / Real.sqrt t) ^ 2 = 1 / t := by
    rw [div_pow, Real.sq_sqrt ht.le, one_pow]
  have h1 : (1 / Real.sqrt t) ^ m ≤ 1 + (1 / t) ^ m := by
    have h := pow_le_one_add_pow_two_mul (1 / Real.sqrt t) m
    rwa [pow_mul, hsq] at h
  have h2 := hC t ht
  calc (1 / Real.sqrt t) ^ m * Real.exp (-(c / t))
      ≤ (1 + (1 / t) ^ m) * Real.exp (-(c / t)) := by gcongr
    _ = Real.exp (-(c / t)) + (1 / t) ^ m * Real.exp (-(c / t)) := by ring
    _ ≤ 1 + C := by linarith

end

end LatticeProb.Analysis.Schauder
