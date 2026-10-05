/-
# Normal comparison (Li--Shao): the covariance scale integral

Route: `scratch/pk/normalcompare-route.md`, item 7.  The final elementary input of the Li--Shao
normal-comparison route is the covariance scale integral

  `∫_0^1 (1 - (t r)²)^{-1/2} dt = arcsin(r)/r ≤ π/2`   (`0 ≤ r < 1`, value `1` at `r = 0`),

whose constant `π/2` gives the route's `C = max 1 (π/2) / (2π)`.  The antiderivative of
`1/√(1-x²)` is `arcsin`, so the substitution `u = t r` gives the closed form, and the convexity
bound `arcsin r ≤ (π/2) r` on `[0,1]` gives the bound.  The rpow form `(1 - (t r)²)^{-1/2}` is the
same integrand by `Real.sqrt_eq_rpow` and `Real.rpow_neg`.

This file lands the scale integral on top of the smart path and the bivariate density bound of
`LatticeProb/Prob/NormalComparison.lean`.  No `External` is touched and no `Prop` is frozen.
-/
import LatticeProb.Prob.NormalComparison

open MeasureTheory
open scoped Interval

namespace LatticeProb

/-- `1/√(1-x²) = x^{-1/2}` for `x > 0`. -/
private theorem rpow_neg_half_eq_one_div_sqrt {x : ℝ} (hx : 0 < x) :
    x ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt x := by
  simpa [Real.sqrt_eq_rpow] using Real.rpow_neg hx.le (1 / 2)

/-- `arcsin r ≤ (π/2) r` for `0 ≤ r ≤ 1` (the convexity bound used to close item 7). -/
private theorem arcsin_le_pi_div_two_mul {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.arcsin r ≤ Real.pi / 2 * r := by
  rw [Real.arcsin_le_iff_le_sin ⟨by linarith, hr1⟩
    ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos, hr1]⟩]
  exact Real.le_sin_mul hr0 hr1

/-- The antiderivative `arcsin` integrates `1/√(1-x²)`:
`∫_0^r 1/√(1-u²) du = arcsin r` for `0 ≤ r < 1`. -/
theorem integral_one_div_sqrt_one_sub_sq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ u in (0 : ℝ)..r, 1 / Real.sqrt (1 - u ^ 2) = Real.arcsin r := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) r,
      HasDerivAt Real.arcsin (1 / Real.sqrt (1 - u ^ 2)) u := by
    intro u hu
    rw [Set.uIcc_of_le hr0] at hu
    exact Real.hasDerivAt_arcsin (by nlinarith [hu.1]) (by nlinarith [hu.2, hr1])
  have hint : IntervalIntegrable (fun u : ℝ => 1 / Real.sqrt (1 - u ^ 2)) volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · exact Real.continuous_sqrt.comp_continuousOn (by fun_prop)
    · intro u hu
      rw [Set.uIcc_of_le hr0] at hu
      exact ne_of_gt (Real.sqrt_pos.mpr (by nlinarith [hu.1, hu.2, hr1]))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, Real.arcsin_zero, sub_zero]

/-- **The scale integral (route item 7), exact form.**  For `0 < r < 1`,
`∫_0^1 1/√(1 - (t r)²) dt = arcsin r / r`. -/
theorem integral_one_div_sqrt_one_sub_sq_mul {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∫ t in (0 : ℝ)..1, 1 / Real.sqrt (1 - (t * r) ^ 2) = Real.arcsin r / r := by
  have hgcont : ContinuousOn (fun u : ℝ => 1 / Real.sqrt (1 - u ^ 2))
      ((fun x : ℝ => x * r) '' Set.uIcc (0 : ℝ) 1) := by
    apply ContinuousOn.div continuousOn_const
    · exact Real.continuous_sqrt.comp_continuousOn (by fun_prop)
    · intro v hv
      rcases hv with ⟨x, hx, rfl⟩
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      exact ne_of_gt (Real.sqrt_pos.mpr (by
        nlinarith [mul_nonneg hx.1 hr0.le, mul_le_of_le_one_left hr0.le hx.2,
          sq_nonneg (x * r), hr0, hr1]))
  have h := intervalIntegral.integral_comp_mul_deriv'
    (f := fun x : ℝ => x * r) (f' := fun _ => r)
    (g := fun u : ℝ => 1 / Real.sqrt (1 - u ^ 2))
    (a := (0 : ℝ)) (b := 1)
    (fun x _ => by simpa using (hasDerivAt_id x).mul_const r)
    (by fun_prop) hgcont
  simp only [Function.comp_apply, zero_mul, one_mul] at h
  rw [integral_one_div_sqrt_one_sub_sq hr0.le hr1] at h
  rw [intervalIntegral.integral_mul_const] at h
  rw [eq_div_iff hr0.ne']
  exact h

/-- **The scale integral (route item 7).**  For `0 ≤ r < 1`,
`∫_0^1 1/√(1 - (t r)²) dt = arcsin r / r ≤ π/2` (with value `1` at `r = 0`). -/
theorem integral_one_div_sqrt_one_sub_sq_mul_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ t in (0 : ℝ)..1, 1 / Real.sqrt (1 - (t * r) ^ 2) ≤ Real.pi / 2 := by
  rcases eq_or_lt_of_le hr0 with h0 | hpos
  · subst h0
    have hone : (fun t : ℝ => 1 / Real.sqrt (1 - (t * 0) ^ 2)) = fun _ => 1 := by
      funext t; simp
    rw [hone, intervalIntegral.integral_const]
    have hpi : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
    simpa using hpi.le
  · rw [integral_one_div_sqrt_one_sub_sq_mul hpos hr1, div_le_iff₀ hpos]
    exact arcsin_le_pi_div_two_mul hr0 hr1.le

/-- **The scale integral in the route's rpow form.**  For `0 ≤ r < 1`,
`∫_0^1 (1 - (t r)²)^{-1/2} dt ≤ π/2`. -/
theorem integral_one_sub_sq_rpow_neg_half_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ t in (0 : ℝ)..1, (1 - (t * r) ^ 2) ^ (-(1 / 2 : ℝ)) ≤ Real.pi / 2 := by
  have hcongr : ∫ t in (0 : ℝ)..1, (1 - (t * r) ^ 2) ^ (-(1 / 2 : ℝ))
      = ∫ t in (0 : ℝ)..1, 1 / Real.sqrt (1 - (t * r) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    change (1 - (t * r) ^ 2) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt (1 - (t * r) ^ 2)
    exact rpow_neg_half_eq_one_div_sqrt (by
      nlinarith [mul_nonneg ht.1 hr0, mul_le_of_le_one_left hr0 ht.2,
        sq_nonneg (t * r), hr0, hr1])
  rw [hcongr]
  exact integral_one_div_sqrt_one_sub_sq_mul_le hr0 hr1

end LatticeProb
