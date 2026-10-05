/-
# Telescoping bound for a difference of finite products of complex numbers

For finite families `a, b : ι → ℂ` the difference `∏ a - ∏ b` is bounded by the sum of the
termwise differences `‖a i - b i‖`, each weighted by the product of the other factors, which are
controlled by their maxima.  No bound on the factors is needed (contrast with
`LatticeProb.norm_prod_sub_prod_le_sum`, which assumes every factor has norm at most `1`):

* `LatticeProb.norm_prod_sub_prod_le_sum_max` — weights `∏_{k ≠ i} max ‖a k‖ ‖b k‖`.
* `LatticeProb.norm_prod_sub_prod_le_sum_of_le` — weights `∏_{k ≠ i} c k` for any
  `c k ≥ max ‖a k‖ ‖b k‖`.
* `LatticeProb.norm_prod_sub_prod_le_sum_exp` — weights `exp (∑_{k ≠ i} u k)` when
  `‖a k‖, ‖b k‖ ≤ exp (u k)`.

The usual application is to characteristic functions of a sum of independent summands compared
with the Gaussian factors `exp (-σ_j² t² / 2)` (non-identically distributed Berry-Esseen).
-/
import Mathlib

namespace LatticeProb

/-- Telescoping bound for a difference of finite products of complex numbers:
`‖∏ a - ∏ b‖ ≤ ∑ i, ‖a i - b i‖ * ∏_{k ≠ i} max ‖a k‖ ‖b k‖`. -/
theorem norm_prod_sub_prod_le_sum_max {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a b : ι → ℂ) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖
      ≤ ∑ i ∈ s, ‖a i - b i‖ * ∏ k ∈ s.erase i, max ‖a k‖ ‖b k‖ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    have hA : ‖∏ k ∈ s, a k‖ ≤ ∏ k ∈ s, max ‖a k‖ ‖b k‖ := by
      rw [norm_prod]
      exact Finset.prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => le_max_left _ _)
    have hsum : ∑ i ∈ s, ‖a i - b i‖ * ∏ k ∈ (insert j s).erase i, max ‖a k‖ ‖b k‖
        = max ‖a j‖ ‖b j‖ * ∑ i ∈ s, ‖a i - b i‖ * ∏ k ∈ s.erase i, max ‖a k‖ ‖b k‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hji : j ≠ i := fun h => hj (h ▸ hi)
      rw [Finset.erase_insert_of_ne hji,
        Finset.prod_insert (fun h => hj (Finset.mem_of_mem_erase h))]
      ring
    have he : a j * (∏ k ∈ s, a k) - b j * (∏ k ∈ s, b k)
        = (a j - b j) * (∏ k ∈ s, a k) + b j * ((∏ k ∈ s, a k) - ∏ k ∈ s, b k) := by ring
    have h1 : ‖(a j - b j) * (∏ k ∈ s, a k)‖
        ≤ ‖a j - b j‖ * ∏ k ∈ s, max ‖a k‖ ‖b k‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hA (norm_nonneg _)
    have h2 : ‖b j * ((∏ k ∈ s, a k) - ∏ k ∈ s, b k)‖
        ≤ max ‖a j‖ ‖b j‖ * ∑ i ∈ s, ‖a i - b i‖ * ∏ k ∈ s.erase i, max ‖a k‖ ‖b k‖ := by
      rw [norm_mul]
      exact mul_le_mul (le_max_right _ _) ih (norm_nonneg _)
        (le_trans (norm_nonneg _) (le_max_left _ _))
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj,
      Finset.erase_insert hj, hsum, he]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-- Variant of `norm_prod_sub_prod_le_sum_max` with a bound `c k ≥ max ‖a k‖ ‖b k‖` on the other
factors: `‖∏ a - ∏ b‖ ≤ ∑ i, ‖a i - b i‖ * ∏_{k ≠ i} c k`. -/
theorem norm_prod_sub_prod_le_sum_of_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a b : ι → ℂ) (c : ι → ℝ) (hc : ∀ k ∈ s, max ‖a k‖ ‖b k‖ ≤ c k) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ ∑ i ∈ s, ‖a i - b i‖ * ∏ k ∈ s.erase i, c k := by
  refine (norm_prod_sub_prod_le_sum_max s a b).trans (Finset.sum_le_sum fun i _ => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact Finset.prod_le_prod (fun k _ => le_trans (norm_nonneg _) (le_max_left _ _))
    (fun k hk => hc k (Finset.mem_of_mem_erase hk))

/-- Exponential form: if `‖a k‖ ≤ exp (u k)` and `‖b k‖ ≤ exp (u k)` for all `k`, then
`‖∏ a - ∏ b‖ ≤ ∑ i, ‖a i - b i‖ * exp (∑_{k ≠ i} u k)`. -/
theorem norm_prod_sub_prod_le_sum_exp {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a b : ι → ℂ) (u : ι → ℝ) (ha : ∀ k ∈ s, ‖a k‖ ≤ Real.exp (u k))
    (hb : ∀ k ∈ s, ‖b k‖ ≤ Real.exp (u k)) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖
      ≤ ∑ i ∈ s, ‖a i - b i‖ * Real.exp (∑ k ∈ s.erase i, u k) := by
  have h := norm_prod_sub_prod_le_sum_of_le s a b (fun k => Real.exp (u k))
    (fun k hk => max_le (ha k hk) (hb k hk))
  simpa only [Real.exp_sum] using h

end LatticeProb
