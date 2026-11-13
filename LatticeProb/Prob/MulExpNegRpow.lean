import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Superpolynomial decay of `r ^ (-a) exp (-c r ^ (-κ))`

For `c, κ > 0` the function `r ↦ r ^ (-a) exp (-c r ^ (-κ))` is, on `(0, 1)`, bounded by
`C r ^ p` for every natural number `p`: it decays faster than any power of `r` as `r → 0`
(`exists_mul_exp_neg_rpow_le`).
-/

open Real

namespace LatticeProb

/-- **Superpolynomial decay.**  For every real `a`, `c, κ > 0`, and every `p : ℕ`, there is `C > 0`
with `r ^ (-a) exp (-(c r ^ (-κ))) ≤ C r ^ p` for all `r ∈ (0, 1)`. -/
lemma exists_mul_exp_neg_rpow_le {a κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r < 1 →
      r ^ (-a) * Real.exp (-(c * r ^ (-κ))) ≤ C * r ^ p := by
  set n : ℕ := ⌈(a + p) / κ⌉₊ with hn
  have hnκ : a + p ≤ κ * n := by
    have := Nat.le_ceil ((a + p) / κ)
    rw [div_le_iff₀ hκ] at this
    linarith
  refine ⟨(n.factorial : ℝ) / c ^ n + 1, by positivity, fun r hr hr1 => ?_⟩
  have hy : 0 ≤ c * r ^ (-κ) := by positivity
  have h1 : (c * r ^ (-κ)) ^ n / n.factorial ≤ Real.exp (c * r ^ (-κ)) :=
    Real.pow_div_factorial_le_exp _ hy n
  have hpos : 0 < (c * r ^ (-κ)) ^ n := by positivity
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h2 : Real.exp (-(c * r ^ (-κ))) ≤ (n.factorial : ℝ) / (c * r ^ (-κ)) ^ n := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) hpos]
    rw [div_le_iff₀ hfac] at h1
    linarith
  have e1 : (r ^ (-κ)) ^ n = r ^ (-(κ * n)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    congr 1
    ring
  have e2 : r ^ (-a) * ((n.factorial : ℝ) / (c * r ^ (-κ)) ^ n)
      = ((n.factorial : ℝ) / c ^ n) * r ^ (κ * n - a) := by
    rw [mul_pow, e1, Real.rpow_sub hr, Real.rpow_neg hr.le, Real.rpow_neg hr.le]
    have h3 : 0 < r ^ (κ * n : ℝ) := by positivity
    have h4 : 0 < c ^ n := by positivity
    field_simp
  have e3 : r ^ (κ * n - a) ≤ r ^ (p : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1.le (by linarith)
  calc r ^ (-a) * Real.exp (-(c * r ^ (-κ)))
      ≤ r ^ (-a) * ((n.factorial : ℝ) / (c * r ^ (-κ)) ^ n) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ((n.factorial : ℝ) / c ^ n) * r ^ (κ * n - a) := e2
    _ ≤ ((n.factorial : ℝ) / c ^ n) * r ^ (p : ℝ) :=
        mul_le_mul_of_nonneg_left e3 (by positivity)
    _ ≤ ((n.factorial : ℝ) / c ^ n + 1) * r ^ p := by
        rw [Real.rpow_natCast]
        nlinarith [pow_pos hr p]

end LatticeProb
