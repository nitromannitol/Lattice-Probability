import Mathlib

/-!
# The Green kernel of planar Brownian motion on a unit time window

The planar heat kernel has density `p_r(x) = (2 π r)⁻¹ exp (-‖x‖² / (2 r))` with respect to Lebesgue measure on `ℂ`.
Its time integral over the window `(0, 1]` (the Green kernel of Brownian motion run for one unit of time) has a
logarithmic singularity at the origin:
`∫_{(0,1]} p_r(x) dr ≤ π⁻¹ (1 + log⁺ (1 / ‖x‖))` for `x ≠ 0` (`lintegral_Ioc_planarHeatDensity_le`).

The proof is elementary. With `a = min 1 ‖x‖²`, on `(0, a]` one has `exp (-t) ≤ 1 / t` for `t = ‖x‖² / (2 r)`, so
the density is at most `1 / (π ‖x‖²)` and the integral over `(0, a]` is at most `a / (π ‖x‖²) ≤ π⁻¹`. On `(a, 1]`
the exponential is at most `1`, and `∫_a^1 (2 π r)⁻¹ dr = (2 π)⁻¹ log (1 / a) = π⁻¹ log⁺ (1 / ‖x‖)`.

Literature: the Green function of two-dimensional Brownian motion, e.g. Mörters-Peres, *Brownian Motion*,
Cambridge University Press 2010, Sec. 3.3 (logarithmic potential in the plane).
-/

namespace LatticeProb

open MeasureTheory Set Real
open scoped ENNReal

/-- **Green kernel bound for planar Brownian motion on a unit window.** For a distance `d > 0`, the integral over
`(0, 1]` of the planar heat density `(2 π r)⁻¹ exp (-d² / (2 r))` is at most `π⁻¹ (1 + log⁺ (1 / d))`, where
`log⁺ (1 / d) = max 0 (-log d)`. -/
theorem lintegral_Ioc_planarHeatDensity_le {d : ℝ} (hd : 0 < d) :
    ∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal ((2 * π * r)⁻¹ * Real.exp (-(d ^ 2) / (2 * r))) ≤
      ENNReal.ofReal (π⁻¹ * (1 + max 0 (-Real.log d))) := by
  have hd2 : 0 < d ^ 2 := by positivity
  set a : ℝ := min 1 (d ^ 2) with ha
  have ha0 : 0 < a := lt_min one_pos hd2
  have ha1 : a ≤ 1 := min_le_left _ _
  have had : a ≤ d ^ 2 := min_le_right _ _
  have hπ : 0 < π := Real.pi_pos
  rw [← Ioc_union_Ioc_eq_Ioc ha0.le ha1]
  refine (lintegral_union_le _ _ _).trans ?_
  -- the part `(0, a]`
  have h1 : ∫⁻ r in Ioc (0 : ℝ) a, ENNReal.ofReal ((2 * π * r)⁻¹ * Real.exp (-(d ^ 2) / (2 * r))) ≤
      ENNReal.ofReal π⁻¹ := by
    have hpt : ∀ r ∈ Ioc (0 : ℝ) a,
        ENNReal.ofReal ((2 * π * r)⁻¹ * Real.exp (-(d ^ 2) / (2 * r))) ≤
          ENNReal.ofReal (1 / (π * d ^ 2)) := by
      intro r hr
      have hr0 : 0 < r := hr.1
      apply ENNReal.ofReal_le_ofReal
      have hx : 0 < d ^ 2 / (2 * r) := by positivity
      have hexp : Real.exp (-(d ^ 2) / (2 * r)) ≤ 2 * r / d ^ 2 := by
        have h := Real.add_one_le_exp (d ^ 2 / (2 * r))
        rw [neg_div, Real.exp_neg]
        calc (Real.exp (d ^ 2 / (2 * r)))⁻¹ ≤ (d ^ 2 / (2 * r))⁻¹ := inv_anti₀ hx (by linarith)
          _ = 2 * r / d ^ 2 := inv_div _ _
      calc (2 * π * r)⁻¹ * Real.exp (-(d ^ 2) / (2 * r)) ≤ (2 * π * r)⁻¹ * (2 * r / d ^ 2) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = 1 / (π * d ^ 2) := by field_simp
    calc ∫⁻ r in Ioc (0 : ℝ) a, ENNReal.ofReal ((2 * π * r)⁻¹ * Real.exp (-(d ^ 2) / (2 * r)))
        ≤ ∫⁻ r in Ioc (0 : ℝ) a, ENNReal.ofReal (1 / (π * d ^ 2)) :=
          setLIntegral_mono' measurableSet_Ioc hpt
      _ = ENNReal.ofReal (1 / (π * d ^ 2)) * ENNReal.ofReal a := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
      _ = ENNReal.ofReal (1 / (π * d ^ 2) * a) := (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal π⁻¹ := by
          apply ENNReal.ofReal_le_ofReal
          calc 1 / (π * d ^ 2) * a ≤ 1 / (π * d ^ 2) * d ^ 2 :=
                mul_le_mul_of_nonneg_left had (by positivity)
            _ = π⁻¹ := by field_simp
  -- the part `(a, 1]`
  have hlogs : (2 * π)⁻¹ * Real.log (1 / a) = π⁻¹ * max 0 (-Real.log d) := by
    rcases le_total d 1 with hd1 | hd1
    · have hd21 : d ^ 2 ≤ 1 := pow_le_one₀ hd.le hd1
      have hmin : a = d ^ 2 := min_eq_right hd21
      have hlog : Real.log d ≤ 0 := Real.log_nonpos hd.le hd1
      rw [hmin, one_div, Real.log_inv, Real.log_pow, max_eq_right (by linarith)]
      push_cast
      field_simp
    · have hmin : a = 1 := min_eq_left (by nlinarith)
      have hlog : 0 ≤ Real.log d := Real.log_nonneg hd1
      rw [hmin, max_eq_left (by linarith)]
      simp
  have h2 : ∫⁻ r in Ioc a 1, ENNReal.ofReal ((2 * π * r)⁻¹ * Real.exp (-(d ^ 2) / (2 * r))) ≤
      ENNReal.ofReal (π⁻¹ * max 0 (-Real.log d)) := by
    have hint : IntegrableOn (fun r : ℝ => (2 * π * r)⁻¹) (Ioc a 1) := by
      have hii : IntervalIntegrable (fun r : ℝ => (2 * π * r)⁻¹) volume a 1 := by
        refine intervalIntegral.intervalIntegrable_inv (fun x hx => ?_) (by fun_prop)
        rw [uIcc_of_le ha1] at hx
        have : 0 < x := lt_of_lt_of_le ha0 hx.1
        positivity
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1 hii
    have hpt : ∀ r ∈ Ioc a 1, ENNReal.ofReal ((2 * π * r)⁻¹ * Real.exp (-(d ^ 2) / (2 * r))) ≤
        ENNReal.ofReal ((2 * π * r)⁻¹) := by
      intro r hr
      have hr0 : 0 < r := lt_of_lt_of_le ha0 hr.1.le
      apply ENNReal.ofReal_le_ofReal
      have hexp : Real.exp (-(d ^ 2) / (2 * r)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ d ^ 2 / (2 * r) := by positivity
        rw [neg_div]; linarith
      calc (2 * π * r)⁻¹ * Real.exp (-(d ^ 2) / (2 * r)) ≤ (2 * π * r)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = (2 * π * r)⁻¹ := mul_one _
    calc ∫⁻ r in Ioc a 1, ENNReal.ofReal ((2 * π * r)⁻¹ * Real.exp (-(d ^ 2) / (2 * r)))
        ≤ ∫⁻ r in Ioc a 1, ENNReal.ofReal ((2 * π * r)⁻¹) := setLIntegral_mono' measurableSet_Ioc hpt
      _ = ENNReal.ofReal (∫ r in Ioc a 1, (2 * π * r)⁻¹) := by
          rw [ofReal_integral_eq_lintegral_ofReal hint]
          refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr => ?_)
          have hr0 : 0 < r := lt_of_lt_of_le ha0 hr.1.le
          positivity
      _ = ENNReal.ofReal ((2 * π)⁻¹ * Real.log (1 / a)) := by
          congr 1
          rw [← intervalIntegral.integral_of_le ha1]
          have : ∀ r : ℝ, (2 * π * r)⁻¹ = (2 * π)⁻¹ * r⁻¹ := fun r => mul_inv _ _
          simp_rw [this]
          rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha0 one_pos]
      _ = ENNReal.ofReal (π⁻¹ * max 0 (-Real.log d)) := by rw [hlogs]
  refine (add_le_add h1 h2).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply le_of_eq
  congr 1
  ring

end LatticeProb
