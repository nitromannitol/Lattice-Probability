/-
# Li--Shao normal comparison: the bivariate density along the path on `[0, T]`

Continuing `LatticeProb/Prob/NormalComparisonScaleFinal.lean` (route items 6 + 7).  The
interpolation assembly integrates the derivative of the orthant probability over `[0, T]` with
`T < 1`, because at `t = 1` the smart path degenerates when a pair correlation `r = S i j / v`
equals `1`.  This file supplies the `[0, T]` version of the integrated bivariate bound for
`0 ≤ r ≤ 1` (the endpoint `r = 1` allowed), together with nonnegativity and continuity of the
bivariate density along the path.

  `∫_0^T p_v(t r; a, b) dt ≤ (4 v)⁻¹ · exp (-(a² + b²) / (2 v (1 + T r)))`,

obtained from `integral_bivariateGaussDensity_le` at correlation `T r < 1` after the substitution
`t = T u`.  No `External` is touched and no `Prop` is frozen.
-/
import Mathlib
import LatticeProb.Prob.NormalComparisonScaleFinal

namespace LatticeProb

/-- The bivariate Gaussian density at positive variance is nonnegative. -/
theorem bivariateGaussDensity_nonneg {v r a b : ℝ} (hv : 0 < v) :
    0 ≤ bivariateGaussDensity v r a b := by
  unfold bivariateGaussDensity
  exact mul_nonneg
    (inv_nonneg.mpr (mul_nonneg (mul_nonneg (by positivity) hv.le) (Real.sqrt_nonneg _)))
    (Real.exp_nonneg _)

/-- `1 - (t r)² > 0` for `t ∈ [0, T]`, `T < 1`, and `0 ≤ r ≤ 1`. -/
private theorem one_sub_sq_pos_Icc {r t T : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hT : T < 1)
    (ht : t ∈ Set.Icc (0 : ℝ) T) : 0 < 1 - (t * r) ^ 2 := by
  have hge : 0 ≤ t * r := mul_nonneg (Set.mem_Icc.mp ht).1 hr0
  have hle : t * r ≤ t := mul_le_of_le_one_right (Set.mem_Icc.mp ht).1 hr1
  nlinarith [hge, hle, (Set.mem_Icc.mp ht).2, hT]

/-- The bivariate density at correlation `t * r` is continuous on `[0, T]` for `T < 1`,
`0 ≤ r ≤ 1`. -/
theorem continuousOn_bivariateGaussDensity_path {v r a b T : ℝ} (hv : 0 < v) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hT : T < 1) :
    ContinuousOn (fun t : ℝ => bivariateGaussDensity v (t * r) a b) (Set.Icc 0 T) := by
  have hden : ContinuousOn (fun t : ℝ => 2 * Real.pi * v * Real.sqrt (1 - (t * r) ^ 2))
      (Set.Icc (0 : ℝ) T) := by fun_prop
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) T,
      2 * Real.pi * v * Real.sqrt (1 - (t * r) ^ 2) ≠ 0 := by
    intro t ht
    exact mul_ne_zero (mul_ne_zero (by positivity) (by positivity))
      (ne_of_gt (Real.sqrt_pos.mpr (one_sub_sq_pos_Icc hr0 hr1 hT ht)))
  have hexp : ContinuousOn (fun t : ℝ => Real.exp
      (-(a ^ 2 - 2 * (t * r) * a * b + b ^ 2) / (2 * v * (1 - (t * r) ^ 2))))
      (Set.Icc (0 : ℝ) T) := by
    apply Real.continuous_exp.comp_continuousOn
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro t ht
      exact mul_ne_zero (by positivity) (ne_of_gt (one_sub_sq_pos_Icc hr0 hr1 hT ht))
  unfold bivariateGaussDensity
  exact (hden.inv₀ hne).mul hexp

/-- The integral over `[0, T]` of the bivariate density along the path is at most
`(4 v)⁻¹ exp (-(a² + b²) / (2 v (1 + T r)))`. -/
theorem integral_bivariateGaussDensity_Icc_le {v r a b T : ℝ} (hv : 0 < v) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hT0 : 0 ≤ T) (hT1 : T < 1) :
    ∫ t in (0 : ℝ)..T, bivariateGaussDensity v (t * r) a b
      ≤ (4 * v)⁻¹ * Real.exp (-(a ^ 2 + b ^ 2) / (2 * v * (1 + T * r))) := by
  rcases hT0.eq_or_lt with hT | hT
  · subst hT
    rw [intervalIntegral.integral_same]
    positivity
  · have hTr0 : 0 ≤ T * r := mul_nonneg hT0 hr0
    have hTr1 : T * r < 1 := lt_of_le_of_lt (mul_le_of_le_one_right hT0 hr1) hT1
    have hsub : ∫ t in (0 : ℝ)..T, bivariateGaussDensity v (t * r) a b
        = T * ∫ u in (0 : ℝ)..1, bivariateGaussDensity v (u * (T * r)) a b := by
      have h := intervalIntegral.integral_comp_mul_left
        (fun t : ℝ => bivariateGaussDensity v (t * r) a b) (a := 0) (b := 1) hT.ne'
      simp only [mul_zero, mul_one, smul_eq_mul] at h
      have h2 : ∫ u in (0 : ℝ)..1, bivariateGaussDensity v (u * (T * r)) a b
          = ∫ u in (0 : ℝ)..1, bivariateGaussDensity v (T * u * r) a b := by
        have hmul : ∀ u : ℝ, u * (T * r) = T * u * r := fun u => by ring
        simp only [hmul]
      rw [h2, h, ← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul]
    have hint := integral_bivariateGaussDensity_le (v := v) (r := T * r) (a := a) (b := b)
      hv hTr0 hTr1
    have hcoef : (2 * Real.pi * v)⁻¹ * (Real.pi / 2) = (4 * v)⁻¹ := by
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have hv' : v ≠ 0 := hv.ne'
      field_simp
      ring
    rw [hcoef] at hint
    have hnn : 0 ≤ (4 * v)⁻¹ * Real.exp (-(a ^ 2 + b ^ 2) / (2 * v * (1 + T * r))) :=
      mul_nonneg (inv_nonneg.mpr (by positivity)) (Real.exp_nonneg _)
    rw [hsub]
    calc T * ∫ u in (0 : ℝ)..1, bivariateGaussDensity v (u * (T * r)) a b
        ≤ T * ((4 * v)⁻¹ * Real.exp (-(a ^ 2 + b ^ 2) / (2 * v * (1 + T * r)))) :=
          mul_le_mul_of_nonneg_left hint hT0
      _ ≤ (4 * v)⁻¹ * Real.exp (-(a ^ 2 + b ^ 2) / (2 * v * (1 + T * r))) :=
          mul_le_of_le_one_left hnn hT1.le

end LatticeProb
