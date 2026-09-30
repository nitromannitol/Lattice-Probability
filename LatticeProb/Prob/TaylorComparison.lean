/-
Third-order Taylor remainders and comparison of probability laws with matching
first and second moments: if two laws agree on the first two moments, the
difference of `∫ f` for any `C³` test function `f` is exactly the difference
of the third-order Taylor remainders, which is the Lindeberg-swap engine
behind a central limit theorem proved by moment matching.

Moved from Divisible-Sandpile-Percolation, `Sandpile/Support/ThirdTaylor.lean`.
This file was already Mathlib-only in the source repository.
-/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open Set MeasureTheory

noncomputable section

namespace LatticeProb

/-- The remainder of `f` at `x` after subtracting its degree-two Taylor
polynomial at `0`. -/
def quadraticRemainder (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x - (f 0 + deriv f 0 * x + deriv (deriv f) 0 * x ^ 2 / 2)

/-- The Lagrange form of the quadratic remainder: it equals the third
derivative at some intermediate point, times `x³/6`. -/
theorem exists_third_order_remainder {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (x : ℝ) :
    ∃ u ∈ uIcc (0 : ℝ) x,
      quadraticRemainder f x = iteratedDeriv 3 f u * x ^ 3 / 6 := by
  by_cases hx : x = 0
  · subst x
    exact ⟨0, by simp, by simp [quadraticRemainder]⟩
  have h0x : (0 : ℝ) ≠ x := Ne.symm hx
  have hu : UniqueDiffOn ℝ (uIcc (0 : ℝ) x) := uniqueDiffOn_uIcc h0x
  have h1 : iteratedDerivWithin 1 f (uIcc (0 : ℝ) x) 0 = deriv f 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu
      ((hf.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).contDiffAt) (left_mem_uIcc),
      iteratedDeriv_one]
  have h2 : iteratedDerivWithin 2 f (uIcc (0 : ℝ) x) 0 = deriv (deriv f) 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu
      ((hf.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).contDiffAt) (left_mem_uIcc),
      iteratedDeriv_succ, iteratedDeriv_one]
  have hp : taylorWithinEval f 2 (uIcc (0 : ℝ) x) 0 x =
      f 0 + deriv f 0 * x + deriv (deriv f) 0 * x ^ 2 / 2 := by
    rw [taylorWithinEval_succ f 1, taylorWithinEval_succ f 0, taylor_within_zero_eval]
    norm_num [h1, h2, smul_eq_mul]
    ring
  obtain ⟨u, hux, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 2) h0x hf.contDiffOn
  refine ⟨u, uIoo_subset_uIcc_self hux, ?_⟩
  rw [hp] at he
  norm_num at he
  exact he

/-- A uniform bound on the third derivative bounds the quadratic remainder. -/
theorem abs_quadraticRemainder_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    {J κ : ℝ} (hJ : 0 ≤ J) (hκ : 0 ≤ κ)
    (hbound : ∀ u, |iteratedDeriv 3 f u| ≤ J * Real.exp (κ * |u|)) (x : ℝ) :
    |quadraticRemainder f x| ≤ J * Real.exp (κ * |x|) * |x| ^ 3 / 6 := by
  obtain ⟨u, hu, he⟩ := exists_third_order_remainder hf x
  have hux : |u| ≤ |x| := by
    simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hu
  rw [he, abs_div, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (abs_nonneg x) 3)
  exact (hbound u).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hux hκ)) hJ)

/-- The quadratic remainder of an integrable function is integrable, given a
first and second moment. -/
theorem integrable_quadraticRemainder {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hf : Integrable f μ) (h1 : Integrable (fun x : ℝ => x) μ)
    (h2 : Integrable (fun x : ℝ => x ^ 2) μ) : Integrable (quadraticRemainder f) μ := by
  exact hf.sub (((integrable_const (f 0)).add (h1.const_mul (deriv f 0))).add
    ((h2.const_mul (deriv (deriv f) 0)).div_const 2))

/-- The integral of the quadratic remainder, in terms of `∫ f` and the first
two moments of `μ`. -/
theorem integral_quadraticRemainder {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hf : Integrable f μ) (h1 : Integrable (fun x : ℝ => x) μ)
    (h2 : Integrable (fun x : ℝ => x ^ 2) μ) :
    (∫ x, quadraticRemainder f x ∂μ) = (∫ x, f x ∂μ) -
      (f 0 + deriv f 0 * (∫ x : ℝ, x ∂μ) + deriv (deriv f) 0 * (∫ x : ℝ, x ^ 2 ∂μ) / 2) := by
  have hp : Integrable (fun x : ℝ => f 0 + deriv f 0 * x + deriv (deriv f) 0 * x ^ 2 / 2) μ :=
    ((integrable_const (f 0)).add (h1.const_mul (deriv f 0))).add
      ((h2.const_mul (deriv (deriv f) 0)).div_const 2)
  calc
    _ = (∫ x, f x ∂μ) - ∫ x : ℝ, f 0 + deriv f 0 * x + deriv (deriv f) 0 * x ^ 2 / 2 ∂μ := by
      convert integral_sub hf hp using 1
      rfl
    _ = _ := by
      have hlin : Integrable (fun x : ℝ => f 0 + deriv f 0 * x) μ :=
        (integrable_const (f 0)).add (h1.const_mul (deriv f 0))
      have hquad : Integrable (fun x : ℝ => deriv (deriv f) 0 * x ^ 2 / 2) μ :=
        (h2.const_mul (deriv (deriv f) 0)).div_const 2
      rw [integral_add hlin hquad]
      have hi : (∫ x : ℝ, f 0 + deriv f 0 * x ∂μ) = f 0 + deriv f 0 * ∫ x : ℝ, x ∂μ := by
        have hh := integral_add (integrable_const (f 0) : Integrable (fun _ : ℝ => f 0) μ)
          (h1.const_mul (deriv f 0))
        simp only [integral_const, probReal_univ, one_smul] at hh
        have hh' : (∫ x : ℝ, f 0 + deriv f 0 * x ∂μ) =
            f 0 + ∫ x : ℝ, deriv f 0 * x ∂μ := by
          convert hh using 1
        rw [hh']
        congr 1
        convert integral_const_mul (μ := μ) (deriv f 0) (fun x : ℝ => x) using 1
      rw [hi, integral_div, integral_const_mul]

/-- **The Lindeberg-swap identity.**  If `μ` and `ν` have the same first two
moments, the difference of `∫ f` for any `C³` (integrable together with its
moments) test function `f` is exactly the difference of the quadratic Taylor
remainders. -/
theorem integral_sub_eq_remainders {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} (hμf : Integrable f μ) (hνf : Integrable f ν)
    (hμ1 : Integrable (fun x : ℝ => x) μ) (hν1 : Integrable (fun x : ℝ => x) ν)
    (hμ2 : Integrable (fun x : ℝ => x ^ 2) μ) (hν2 : Integrable (fun x : ℝ => x ^ 2) ν)
    (he1 : (∫ x : ℝ, x ∂μ) = ∫ x : ℝ, x ∂ν)
    (he2 : (∫ x : ℝ, x ^ 2 ∂μ) = ∫ x : ℝ, x ^ 2 ∂ν) :
    (∫ x, f x ∂ν) - (∫ x, f x ∂μ) =
      (∫ x, quadraticRemainder f x ∂ν) - (∫ x, quadraticRemainder f x ∂μ) := by
  rw [integral_quadraticRemainder hνf hν1 hν2, integral_quadraticRemainder hμf hμ1 hμ2,
    he1, he2]
  ring

/-- A uniform sub-exponential bound on the third derivative bounds the
integral of the absolute quadratic remainder. -/
theorem integral_abs_quadraticRemainder_le {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (hμf : Integrable f μ) (hμ1 : Integrable (fun x : ℝ => x) μ)
    (hμ2 : Integrable (fun x : ℝ => x ^ 2) μ)
    {J κ T : ℝ} (hJ : 0 ≤ J) (hκ : 0 ≤ κ)
    (hbound : ∀ u, |iteratedDeriv 3 f u| ≤ J * Real.exp (κ * |u|))
    (hW : Integrable (fun x : ℝ => |x| ^ 3 * Real.exp (κ * |x|)) μ)
    (hT : (∫ x : ℝ, |x| ^ 3 * Real.exp (κ * |x|) ∂μ) ≤ T) :
    (∫ x, |quadraticRemainder f x| ∂μ) ≤ J * T / 6 := by
  calc
    _ ≤ ∫ x : ℝ, (J / 6) * (|x| ^ 3 * Real.exp (κ * |x|)) ∂μ := by
      apply integral_mono (integrable_quadraticRemainder hμf hμ1 hμ2).abs (hW.const_mul _)
      intro x
      convert abs_quadraticRemainder_le hf hJ hκ hbound x using 1 <;> first | rfl | ring
    _ = J / 6 * (∫ x : ℝ, |x| ^ 3 * Real.exp (κ * |x|) ∂μ) := integral_const_mul _ _
    _ ≤ J * T / 6 := by
      convert mul_le_mul_of_nonneg_left hT (div_nonneg hJ (by norm_num : (0 : ℝ) ≤ 6)) using 1 <;> first | rfl | ring

/-- **The third-order comparison bound.**  If `μ` and `ν` share their first two
moments and both have a sub-exponentially controlled third absolute moment
`T` for the test function `f`, then `|∫ f dν - ∫ f dμ| ≤ J T / 3`. -/
theorem integral_comparison_third_order {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (hμf : Integrable f μ) (hνf : Integrable f ν)
    (hμ1 : Integrable (fun x : ℝ => x) μ) (hν1 : Integrable (fun x : ℝ => x) ν)
    (hμ2 : Integrable (fun x : ℝ => x ^ 2) μ) (hν2 : Integrable (fun x : ℝ => x ^ 2) ν)
    (he1 : (∫ x : ℝ, x ∂μ) = ∫ x : ℝ, x ∂ν)
    (he2 : (∫ x : ℝ, x ^ 2 ∂μ) = ∫ x : ℝ, x ^ 2 ∂ν)
    {J κ T : ℝ} (hJ : 0 ≤ J) (hκ : 0 ≤ κ)
    (hbound : ∀ u, |iteratedDeriv 3 f u| ≤ J * Real.exp (κ * |u|))
    (hμW : Integrable (fun x : ℝ => |x| ^ 3 * Real.exp (κ * |x|)) μ)
    (hνW : Integrable (fun x : ℝ => |x| ^ 3 * Real.exp (κ * |x|)) ν)
    (hμT : (∫ x : ℝ, |x| ^ 3 * Real.exp (κ * |x|) ∂μ) ≤ T)
    (hνT : (∫ x : ℝ, |x| ^ 3 * Real.exp (κ * |x|) ∂ν) ≤ T) :
    |(∫ x, f x ∂ν) - (∫ x, f x ∂μ)| ≤ J * T / 3 := by
  rw [integral_sub_eq_remainders hμf hνf hμ1 hν1 hμ2 hν2 he1 he2]
  apply (abs_sub _ _).trans
  have hμ := (abs_integral_le_integral_abs (μ := μ) (f := quadraticRemainder f)).trans
    (integral_abs_quadraticRemainder_le hf hμf hμ1 hμ2 hJ hκ hbound hμW hμT)
  have hν := (abs_integral_le_integral_abs (μ := ν) (f := quadraticRemainder f)).trans
    (integral_abs_quadraticRemainder_le hf hνf hν1 hν2 hJ hκ hbound hνW hνT)
  linarith

end LatticeProb
