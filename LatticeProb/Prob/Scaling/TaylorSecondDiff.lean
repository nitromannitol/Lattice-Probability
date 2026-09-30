/- Symmetric second differences from Taylor's theorem with Lagrange remainder.

Moved from Parking-Sharpness.
-/
import Mathlib

open Set
noncomputable section

namespace LatticeProb.Scaling.TaylorSecondDiff

/-- The zeroth-order Taylor polynomial evaluated anywhere is the base value: no linear term to
subtract. -/
theorem taylorWithinEval_zero_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (s : Set ℝ) (x₀ x : ℝ) : taylorWithinEval f 0 s x₀ x = f x₀ := by
  simp [taylorWithinEval, taylorWithin, taylorCoeffWithin]

/-- **Taylor's theorem at order 1 with the Lagrange remainder, stated additively.** For `g`
twice continuously differentiable and `a ≠ b`, `g b` differs from its first-order Taylor
approximation at `a` by exactly `g''(x') (b-a)²/2` for some `x'` strictly between `a` and `b`.
A repackaging of Mathlib's `taylor_mean_remainder_lagrange` at `n = 1`, unfolding the Taylor
polynomial and identifying the within-derivatives with the plain derivatives of the globally
smooth `g`. -/
theorem first_order_lagrange {g : ℝ → ℝ} (hg : ContDiff ℝ (2 : ℕ) g) {a b : ℝ} (hab : a ≠ b) :
    ∃ x' ∈ uIoo a b,
      g b - (g a + deriv g a * (b - a)) = deriv (deriv g) x' * (b - a) ^ 2 / 2 := by
  have huniq : UniqueDiffOn ℝ (uIcc a b) := uniqueDiffOn_uIcc hab
  have hg1 : ContDiff ℝ (1 : ℕ) g := hg.of_le (by norm_num)
  have hgder : ContDiff ℝ (1 : ℕ) (deriv g) := hg.deriv'
  have hf : ContDiffOn ℝ (1 : ℕ) g (uIcc a b) := hg1.contDiffOn
  have hderiv1 : ∀ {t : ℝ}, t ∈ uIcc a b →
      iteratedDerivWithin 1 g (uIcc a b) t = deriv g t := by
    intro t ht
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq hg1.contDiffAt ht, iteratedDeriv_one]
  have hf' : DifferentiableOn ℝ (iteratedDerivWithin 1 g (uIcc a b)) (uIoo a b) := by
    have heqOn : Set.EqOn (iteratedDerivWithin 1 g (uIcc a b)) (deriv g) (uIoo a b) :=
      fun t ht => hderiv1 (uIoo_subset_uIcc_self ht)
    refine DifferentiableOn.congr ?_ heqOn
    exact (hgder.differentiable (by norm_num)).differentiableOn
  obtain ⟨x', hx', heq⟩ := taylor_mean_remainder_lagrange hab hf hf'
  refine ⟨x', hx', ?_⟩
  rw [taylorWithinEval_succ, taylorWithinEval_zero_eq, hderiv1 (left_mem_uIcc)] at heq
  have h2 : iteratedDerivWithin (1 + 1) g (uIcc a b) x' = deriv (deriv g) x' := by
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq hg.contDiffAt (uIoo_subset_uIcc_self hx')]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2] at heq
  simp only [Nat.factorial_zero, Nat.cast_one, mul_one, smul_eq_mul] at heq
  linarith [heq]

/-- **The symmetric second difference, exactly, via two applications of `first_order_lagrange`.**
`g(x₀+h) + g(x₀-h) - 2g(x₀) = h²/2 (g''(ξ1) + g''(ξ2))` for some `ξ1` strictly between `x₀` and
`x₀+h`, and `ξ2` strictly between `x₀-h` and `x₀`. This is the one-variable core of the
discrete-Laplacian second-order accuracy: the linear terms of the two Taylor expansions cancel
on addition, leaving only the second-derivative remainders. -/
theorem exists_symm_second_diff_eq {g : ℝ → ℝ} (hg : ContDiff ℝ (2 : ℕ) g) (x₀ : ℝ) {h : ℝ}
    (hh : 0 < h) :
    ∃ ξ1 ∈ Ioo x₀ (x₀ + h), ∃ ξ2 ∈ Ioo (x₀ - h) x₀,
      g (x₀ + h) + g (x₀ - h) - 2 * g x₀
        = h ^ 2 / 2 * (deriv (deriv g) ξ1 + deriv (deriv g) ξ2) := by
  obtain ⟨ξ1, hξ1, heq1⟩ := first_order_lagrange hg (a := x₀) (b := x₀ + h) (by
    intro hcontra; linarith)
  obtain ⟨ξ2, hξ2, heq2⟩ := first_order_lagrange hg (a := x₀) (b := x₀ - h) (by
    intro hcontra; linarith)
  have e1 : uIoo x₀ (x₀ + h) = Ioo x₀ (x₀ + h) := by
    unfold uIoo
    rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  have e2 : uIoo x₀ (x₀ - h) = Ioo (x₀ - h) x₀ := by
    unfold uIoo
    rw [min_eq_right (by linarith), max_eq_left (by linarith)]
  rw [e1] at hξ1
  rw [e2] at hξ2
  refine ⟨ξ1, hξ1, ξ2, hξ2, ?_⟩
  nlinarith [heq1, heq2]

end LatticeProb.Scaling.TaylorSecondDiff

end
