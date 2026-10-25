module

public import LatticeProb.Prob.McLeish.ExpRemainder
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

/-!
# Deterministic remainder estimates for products of exponential factors

For real numbers `x i` with `|x i| ≤ 1 / 2`, the exponential of `Complex.I` times their sum
equals the product of the factors `1 + Complex.I * x i`, times a Gaussian-type factor, up to an
explicit remainder of size at most `2 * ∑ |x i| ^ 3`. Applying this to the scaled values `t * y k`
gives a quantitative comparison of the normalised characteristic-type quotient with a Gaussian,
with error `4 * |t| ^ 3 * m * ∑ y k ^ 2` under explicit smallness conditions.

## Main results

* `sum_abs_pow_three_le` : `∑ |x i| ^ 3 ≤ m * ∑ x i ^ 2` when every `|x i| ≤ m`.
* `exp_I_mul_sum_eq_prod_mul_exp` : the factorisation of `exp (I * ∑ x i)` over a finite set.
* `norm_exp_div_prod_sub_le` : the comparison of the quotient with a Gaussian.
-/

namespace LatticeProb.McLeish

/-- The third power of the absolute values of finitely many reals is bounded by the sum of
their squares, weighted by a common bound `m` on the absolute values. -/
theorem sum_abs_pow_three_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) (m : ℝ)
    (hm : ∀ i ∈ s, |x i| ≤ m) :
    ∑ i ∈ s, |x i| ^ 3 ≤ m * ∑ i ∈ s, x i ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have h3 : |x i| ^ 3 = |x i| * x i ^ 2 := by
    rw [← sq_abs (x i)]
    ring
  rw [h3]
  exact mul_le_mul_of_nonneg_right (hm i hi) (sq_nonneg _)

/-- Factorisation of `Complex.exp (Complex.I * ∑ x i)` over a finite set of indices, for
`|x i| ≤ 1 / 2`, with remainder bounded by `2 * ∑ |x i| ^ 3`. -/
theorem exp_I_mul_sum_eq_prod_mul_exp {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, |x i| ≤ 1 / 2) :
    ∃ R : ℂ, ‖R‖ ≤ 2 * ∑ i ∈ s, |x i| ^ 3 ∧
      Complex.exp (Complex.I * ((∑ i ∈ s, x i : ℝ) : ℂ)) =
        (∏ i ∈ s, (1 + Complex.I * (x i : ℂ))) *
          Complex.exp (-((∑ i ∈ s, x i ^ 2 : ℝ) : ℂ) / 2 + R) := by
  classical
  revert hx
  induction s using Finset.induction_on with
  | empty => intro _; exact ⟨0, by simp, by simp⟩
  | insert a s ha ih =>
    intro hx
    obtain ⟨R, hR, hEq⟩ := ih fun i hi => hx i (Finset.mem_insert_of_mem hi)
    obtain ⟨r, hr, hra⟩ :=
      exp_I_mul_eq_one_add_mul_exp (x a) (hx a (Finset.mem_insert_self a s))
    have hexp_arg : -((∑ i ∈ insert a s, x i ^ 2 : ℝ) : ℂ) / 2 + (r + R)
        = (-(x a : ℂ) ^ 2 / 2 + r) + (-((∑ i ∈ s, x i ^ 2 : ℝ) : ℂ) / 2 + R) := by
      rw [Finset.sum_insert ha]
      push_cast
      ring
    have hL : Complex.I * ((∑ i ∈ insert a s, x i : ℝ) : ℂ)
        = Complex.I * (x a : ℂ) + Complex.I * ((∑ i ∈ s, x i : ℝ) : ℂ) := by
      rw [Finset.sum_insert ha]
      push_cast
      ring
    refine ⟨r + R, ?_, ?_⟩
    · rw [Finset.sum_insert ha]
      have h1 := norm_add_le r R
      linarith
    · rw [hL, Complex.exp_add (Complex.I * (x a : ℂ)), hra, hEq, Finset.prod_insert ha,
        hexp_arg, Complex.exp_add (-(x a : ℂ) ^ 2 / 2 + r)]
      ring

/-- Comparison of the quotient `exp (I * t * ∑ y k) / ∏ (1 + I * t * y k)` with the Gaussian
factor `exp (-t ^ 2 * ∑ y k ^ 2 / 2)`. Under the bounds `|y k| ≤ m` for `k < n`,
`|t| * m ≤ 1 / 2` and `2 * |t| ^ 3 * m * ∑ y k ^ 2 ≤ 1`, the difference of the two has norm at
most `4 * |t| ^ 3 * m * ∑ y k ^ 2`. -/
theorem norm_exp_div_prod_sub_le (y : ℕ → ℝ) (t m : ℝ) (n : ℕ)
    (hm : ∀ k < n, |y k| ≤ m) (ht : |t| * m ≤ 1 / 2)
    (hρ : 2 * |t| ^ 3 * m * ∑ k ∈ Finset.range n, y k ^ 2 ≤ 1) :
    ‖Complex.exp (Complex.I * ((t * ∑ k ∈ Finset.range n, y k : ℝ) : ℂ)) /
          ∏ k ∈ Finset.range n, (1 + Complex.I * ((t * y k : ℝ) : ℂ)) -
        Complex.exp (((-(t ^ 2 * ∑ k ∈ Finset.range n, y k ^ 2) / 2 : ℝ) : ℂ))‖ ≤
      4 * |t| ^ 3 * m * ∑ k ∈ Finset.range n, y k ^ 2 := by
  have hx' : ∀ k ∈ Finset.range n, |t * y k| ≤ |t| * m := fun k hk => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hm k (Finset.mem_range.mp hk)) (abs_nonneg t)
  have hx : ∀ k ∈ Finset.range n, |t * y k| ≤ 1 / 2 := fun k hk => (hx' k hk).trans ht
  obtain ⟨R, hR, hEq⟩ : ∃ R : ℂ, ‖R‖ ≤ 2 * ∑ k ∈ Finset.range n, |t * y k| ^ 3 ∧
      Complex.exp (Complex.I * ((∑ k ∈ Finset.range n, t * y k : ℝ) : ℂ)) =
        (∏ k ∈ Finset.range n, (1 + Complex.I * ((t * y k : ℝ) : ℂ))) *
          Complex.exp (-((∑ k ∈ Finset.range n, (t * y k) ^ 2 : ℝ) : ℂ) / 2 + R) :=
    exp_I_mul_sum_eq_prod_mul_exp (Finset.range n) (fun k => t * y k) hx
  have h3 : ∑ k ∈ Finset.range n, |t * y k| ^ 3
      ≤ |t| * m * ∑ k ∈ Finset.range n, (t * y k) ^ 2 :=
    sum_abs_pow_three_le (Finset.range n) (fun k => t * y k) (|t| * m) hx'
  have hsum : ∑ k ∈ Finset.range n, t * y k = t * ∑ k ∈ Finset.range n, y k := by
    rw [Finset.mul_sum]
  have h4 : ∑ k ∈ Finset.range n, (t * y k) ^ 2
      = t ^ 2 * ∑ k ∈ Finset.range n, y k ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsum, h4] at hEq
  rw [h4] at h3
  set S := ∑ k ∈ Finset.range n, y k ^ 2 with hS_def
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => sq_nonneg (y k)
  have hk : |t| * m * (t ^ 2 * S) = |t| ^ 3 * m * S := by
    rw [← sq_abs t]
    ring
  have hRb : ‖R‖ ≤ 2 * |t| ^ 3 * m * S := by
    linarith
  have hR1 : ‖R‖ ≤ 1 := by
    linarith
  have hcast : -((t ^ 2 * S : ℝ) : ℂ) / 2 = ((-(t ^ 2 * S) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hP : ∏ k ∈ Finset.range n, (1 + Complex.I * ((t * y k : ℝ) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => one_add_I_mul_ne_zero (t * y k)
  have hq : Complex.exp (Complex.I * ((t * ∑ k ∈ Finset.range n, y k : ℝ) : ℂ)) /
        ∏ k ∈ Finset.range n, (1 + Complex.I * ((t * y k : ℝ) : ℂ))
      = Complex.exp (((-(t ^ 2 * S) / 2 : ℝ) : ℂ) + R) := by
    rw [hEq, hcast, mul_div_cancel_left₀ _ hP]
  have ha : -(t ^ 2 * S) / 2 ≤ 0 := by
    have := mul_nonneg (sq_nonneg t) hS
    linarith
  have hexp1 : Real.exp (-(t ^ 2 * S) / 2) ≤ 1 := Real.exp_le_one_iff.mpr ha
  have hsplit : Complex.exp (((-(t ^ 2 * S) / 2 : ℝ) : ℂ) + R)
      - Complex.exp (((-(t ^ 2 * S) / 2 : ℝ) : ℂ))
      = Complex.exp (((-(t ^ 2 * S) / 2 : ℝ) : ℂ)) * (Complex.exp R - 1) := by
    rw [Complex.exp_add]
    ring
  have hE : ‖Complex.exp R - 1‖ ≤ 2 * (2 * |t| ^ 3 * m * S) :=
    (Complex.norm_exp_sub_one_le hR1).trans (by linarith)
  rw [hq, hsplit, norm_mul, Complex.norm_exp_ofReal]
  have := mul_le_mul hexp1 hE (norm_nonneg _) zero_le_one
  linarith

end LatticeProb.McLeish
