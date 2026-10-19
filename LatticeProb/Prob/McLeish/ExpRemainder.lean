import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# A third-order factorisation of the complex exponential

For real `x` with `|x| ≤ 1/2`, the number `Complex.exp (Complex.I * x)` factors as
`(1 + Complex.I * x) * Complex.exp (-(x : ℂ) ^ 2 / 2 + r)` for a complex number `r` with
`‖r‖ ≤ 2 * |x| ^ 3`. The remainder `r` is produced explicitly as a logarithm, and the bound
combines the third-order Taylor estimate for `Complex.exp` with the estimate for `Complex.log (1 + z)`.

## Main results

* `exp_I_mul_eq_one_add_mul_exp` : the factorisation with the remainder bound.
-/

namespace LatticeProb.McLeish

/-- For real `x`, the number `1 + Complex.I * x` is nonzero, since its real part is `1`. -/
lemma one_add_I_mul_ne_zero (x : ℝ) : (1 : ℂ) + Complex.I * x ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  simp at h1

/-- Third-order Taylor estimate for `Complex.exp (Complex.I * x)` with constant `2 / 9`. -/
lemma norm_exp_I_mul_sub_taylor_le {x : ℝ} (hx : |x| ≤ 1) :
    ‖Complex.exp (Complex.I * x) - (1 + Complex.I * x - (x : ℂ) ^ 2 / 2)‖ ≤ 2 / 9 * |x| ^ 3 := by
  have hnorm : ‖Complex.I * (x : ℂ)‖ = |x| := by simp
  have h := Complex.exp_bound (x := Complex.I * (x : ℂ)) (n := 3) (by rw [hnorm]; exact hx)
    (by norm_num)
  have hs : ∑ m ∈ Finset.range 3, (Complex.I * (x : ℂ)) ^ m / (m.factorial : ℂ)
      = 1 + Complex.I * x - (x : ℂ) ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
    linear_combination ((x : ℂ) ^ 2 / 2) * Complex.I_sq
  rw [hs, hnorm] at h
  norm_num at h ⊢
  linarith

/-- The remainder of `Complex.exp (Complex.I * x)` after dividing by `1 + Complex.I * x`. -/
lemma norm_div_one_add_I_mul_sub_le {x : ℝ} (hx : |x| ≤ 1) :
    ‖Complex.exp (Complex.I * x) / (1 + Complex.I * x) - 1 + (x : ℂ) ^ 2 / 2‖
      ≤ 13 / 18 * |x| ^ 3 := by
  have hz : (1 : ℂ) + Complex.I * x ≠ 0 := one_add_I_mul_ne_zero x
  have hdenom : 1 ≤ ‖(1 : ℂ) + Complex.I * x‖ := by
    have h1 := Complex.abs_re_le_norm ((1 : ℂ) + Complex.I * x)
    simpa using h1
  have hnum : Complex.exp (Complex.I * x) / (1 + Complex.I * x) - 1 + (x : ℂ) ^ 2 / 2
      = (Complex.exp (Complex.I * x) - (1 + Complex.I * x - (x : ℂ) ^ 2 / 2)
          + Complex.I * ((x : ℂ) ^ 3 / 2)) / (1 + Complex.I * x) := by
    field_simp
    ring
  have hI : ‖Complex.I * ((x : ℂ) ^ 3 / 2)‖ = |x| ^ 3 / 2 := by
    simp [norm_pow]
  have hN : ‖Complex.exp (Complex.I * x) - (1 + Complex.I * x - (x : ℂ) ^ 2 / 2)
      + Complex.I * ((x : ℂ) ^ 3 / 2)‖ ≤ 13 / 18 * |x| ^ 3 := by
    have h1 := norm_add_le (Complex.exp (Complex.I * x) - (1 + Complex.I * x - (x : ℂ) ^ 2 / 2))
      (Complex.I * ((x : ℂ) ^ 3 / 2))
    have h2 := norm_exp_I_mul_sub_taylor_le hx
    linarith
  rw [hnum, norm_div]
  have h3 : 0 ≤ 13 / 18 * |x| ^ 3 := by positivity
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- Factorisation of `Complex.exp (Complex.I * x)` for `|x| ≤ 1/2`, with remainder `2 |x|^3`. -/
theorem exp_I_mul_eq_one_add_mul_exp (x : ℝ) (hx : |x| ≤ 1 / 2) :
    ∃ r : ℂ, ‖r‖ ≤ 2 * |x| ^ 3 ∧
      Complex.exp (Complex.I * x) = (1 + Complex.I * x) * Complex.exp (-(x : ℂ) ^ 2 / 2 + r) := by
  have hz : (1 : ℂ) + Complex.I * x ≠ 0 := one_add_I_mul_ne_zero x
  have hu0 : 0 ≤ |x| := abs_nonneg x
  have hu1 : |x| ≤ 1 := by linarith
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = Complex.exp (Complex.I * x) / (1 + Complex.I * x) - 1 :=
    ⟨_, rfl⟩
  have hw1 : 1 + w = Complex.exp (Complex.I * x) / (1 + Complex.I * x) := by
    rw [hw]
    ring
  have hne : 1 + w ≠ 0 := by
    rw [hw1]
    exact div_ne_zero (Complex.exp_ne_zero _) hz
  have hkey : ‖w + (x : ℂ) ^ 2 / 2‖ ≤ 13 / 18 * |x| ^ 3 := by
    rw [hw]
    exact norm_div_one_add_I_mul_sub_le hu1
  have hsq : ‖(x : ℂ) ^ 2 / 2‖ = |x| ^ 2 / 2 := by
    simp [norm_pow]
  have hwn : ‖w‖ ≤ |x| ^ 2 := by
    have h1 : ‖w‖ ≤ ‖w + (x : ℂ) ^ 2 / 2‖ + ‖(x : ℂ) ^ 2 / 2‖ := by
      have h0 := norm_sub_le (w + (x : ℂ) ^ 2 / 2) ((x : ℂ) ^ 2 / 2)
      rwa [show w + (x : ℂ) ^ 2 / 2 - (x : ℂ) ^ 2 / 2 = w by ring] at h0
    rw [hsq] at h1
    nlinarith [mul_nonneg (sq_nonneg |x|) (by linarith : (0 : ℝ) ≤ 1 / 2 - |x|)]
  have hwlt : ‖w‖ < 1 := by
    nlinarith
  have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
    have h12 : (1 : ℝ) / 2 ≤ 1 - ‖w‖ := by nlinarith
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) h12
    norm_num at this
    exact this
  have hlog : ‖Complex.log (1 + w) - w‖ ≤ ‖w‖ ^ 2 := by
    have h1 := Complex.norm_log_one_add_sub_self_le hwlt
    have h2 : ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 ≤ ‖w‖ ^ 2 * 2 / 2 := by
      gcongr
    have h3 : ‖w‖ ^ 2 * 2 / 2 = ‖w‖ ^ 2 := by ring
    linarith
  have hw2 : ‖w‖ ^ 2 ≤ |x| ^ 4 := by
    have := pow_le_pow_left₀ (norm_nonneg w) hwn 2
    nlinarith
  have hu3 : 0 ≤ |x| ^ 3 := pow_nonneg hu0 3
  have hx4 : |x| ^ 4 ≤ |x| ^ 3 / 2 := by
    nlinarith
  refine ⟨Complex.log (1 + w) + (x : ℂ) ^ 2 / 2, ?_, ?_⟩
  · have hdecomp : Complex.log (1 + w) + (x : ℂ) ^ 2 / 2
        = (Complex.log (1 + w) - w) + (w + (x : ℂ) ^ 2 / 2) := by
      ring
    rw [hdecomp]
    refine (norm_add_le _ _).trans ?_
    linarith
  · have hexp : Complex.exp (-(x : ℂ) ^ 2 / 2 + (Complex.log (1 + w) + (x : ℂ) ^ 2 / 2))
        = 1 + w := by
      rw [show -(x : ℂ) ^ 2 / 2 + (Complex.log (1 + w) + (x : ℂ) ^ 2 / 2)
          = Complex.log (1 + w) by ring]
      exact Complex.exp_log hne
    rw [hexp, hw1]
    field_simp

end LatticeProb.McLeish
