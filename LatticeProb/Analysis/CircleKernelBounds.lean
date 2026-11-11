import Mathlib

/-!
# Logarithmic kernel bounds on circles

For a centre `z : ℂ`, a point `u : ℂ`, a radius `R > 0` and a circle `∂B_t(z)`, the logarithmic kernel
`K(u, v) = log (R / ‖u - v‖) + 1` is interval integrable along the circle, is bounded below by `1 - log 4`
on the annulus `‖u - v‖ ≤ 4R`, and has an explicit circle average. The statements below are general: they
involve no constant other than the logarithm, the circle map and Mathlib's circle averages.

Main results:
* `ae_circleMap_ne`: for a fixed point `u`, almost every parameter of a circle avoids `u`;
* `circleAverage_congr_of_ne`: a circle average does not see the value of the integrand at one point;
* `intervalIntegrable_kernel_slice`: `θ ↦ K(u, circleMap z t θ)` is interval integrable on `[0, 2π]`;
* `kernel_ge_neg`: `K(u, v) ≥ 1 - log 4` when `‖u - v‖ ≤ 4R`;
* `circleAverage_kernel_eq` and `circleAverage_kernel_le`: the circle average of the kernel over the circle
  of radius `3R/2` (closed form and upper bound);
* `integral_kernel_Ioc_le` and `integral_norm_kernel_le`: bounds on the integral over `(0, 2π]`.

The circle average of `log ‖· - a‖` is Mathlib's `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`.
-/

open MeasureTheory Real Set Metric

namespace LatticeProb.CircleKernelBounds

/-- The distance of a point of the circle `∂B_t(z)` from its centre is `|t|`. -/
theorem norm_circleMap_sub_center' (z : ℂ) (t θ : ℝ) : ‖z - circleMap z t θ‖ = |t| := by
  rw [norm_sub_rev, circleMap_sub_center, norm_circleMap_zero]

/-- `1 ≤ log 4`, so that `log 4 - 1 ≥ 0`. -/
theorem one_le_log_four : 1 ≤ Real.log 4 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have := Real.log_two_gt_d9
  linarith

/-- The kernel `log (R / ‖u - v‖) + 1` is bounded below by `1 - log 4` when `‖u - v‖ ≤ 4R`. -/
theorem kernel_ge_neg {R : ℝ} {u v : ℂ} (huv : ‖u - v‖ ≤ 4 * R) :
    -(Real.log 4 - 1) ≤ Real.log (R / ‖u - v‖) + 1 := by
  rcases eq_or_ne ‖u - v‖ 0 with h0 | h0
  · rw [h0, div_zero, Real.log_zero]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    linarith
  · have hpos : 0 < ‖u - v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have h4 : (1 / 4 : ℝ) ≤ R / ‖u - v‖ := by
      rw [le_div_iff₀ hpos]
      linarith
    have hl := Real.log_le_log (by norm_num) h4
    have hl4 : Real.log (1 / 4) = -Real.log 4 := by
      rw [one_div, Real.log_inv]
    linarith

/-- A circle average does not see the value of the integrand at a single point `u` of the circle. -/
theorem circleAverage_congr_of_ne {f g : ℂ → ℝ} {z u : ℂ} {t : ℝ} (ht : t ≠ 0)
    (h : ∀ v : ℂ, v ≠ u → f v = g v) :
    circleAverage f z t = circleAverage g z t := by
  simp only [circleAverage_def]
  congr 1
  apply intervalIntegral.integral_congr_ae
  have hnull : volume {θ : ℝ | θ ∈ Set.uIoc 0 (2 * π) ∧ circleMap z t θ = u} = 0 := by
    apply Set.Subsingleton.measure_zero _ volume
    intro a ha b hb
    exact injOn_circleMap_of_abs_sub_le ht (by rw [zero_sub, abs_neg, abs_of_pos (by positivity)])
      ha.1 hb.1 (ha.2.trans hb.2.symm)
  rw [ae_iff]
  refine measure_mono_null ?_ hnull
  intro θ hθ
  simp only [Set.mem_ofPred_eq, not_imp] at hθ
  exact ⟨hθ.1, by by_contra hc; exact hθ.2 (h _ hc)⟩

/-- For a fixed point `u`, almost every `θ ∈ (0, 2π]` satisfies `circleMap z t θ ≠ u`. -/
theorem ae_circleMap_ne {z u : ℂ} {t : ℝ} (ht : t ≠ 0) :
    ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Set.uIoc 0 (2 * π) → circleMap z t θ ≠ u := by
  have hnull : volume {θ : ℝ | θ ∈ Set.uIoc 0 (2 * π) ∧ circleMap z t θ = u} = 0 := by
    apply Set.Subsingleton.measure_zero _ volume
    intro a ha b hb
    exact injOn_circleMap_of_abs_sub_le ht (by rw [zero_sub, abs_neg, abs_of_pos (by positivity)])
      ha.1 hb.1 (ha.2.trans hb.2.symm)
  rw [ae_iff]
  refine measure_mono_null ?_ hnull
  intro θ hθ
  simp only [Set.mem_ofPred_eq, not_imp, ne_eq, not_not] at hθ
  exact hθ

/-- For fixed `u`, the kernel `θ ↦ log (R / ‖u - circleMap z t θ‖) + 1` is interval integrable over `[0, 2π]`. -/
theorem intervalIntegrable_kernel_slice {z u : ℂ} {R t : ℝ} (hR : 0 < R) (ht : t ≠ 0) :
    IntervalIntegrable (fun θ : ℝ => Real.log (R / ‖u - circleMap z t θ‖) + 1) volume 0 (2 * π) := by
  have h1 : IntervalIntegrable (fun θ : ℝ => (Real.log R + 1) - Real.log ‖circleMap z t θ - u‖)
      volume 0 (2 * π) :=
    intervalIntegrable_const.sub (circleIntegrable_log_norm_sub_const (c := z) (a := u) t)
  refine h1.congr_ae ?_
  filter_upwards [(ae_restrict_iff' measurableSet_uIoc).2 (ae_circleMap_ne (z := z) (u := u) ht)]
    with θ hne
  have huv : ‖u - circleMap z t θ‖ ≠ 0 := by
    rw [norm_ne_zero_iff, sub_ne_zero]
    exact hne.symm
  rw [Real.log_div hR.ne' huv, norm_sub_rev]
  ring

/-- **Closed form of the circle average of the kernel.** The circle of radius `3R/2` about `z`, with the
kernel centred at `u`. -/
theorem circleAverage_kernel_eq {z u : ℂ} {R : ℝ} (hR : 0 < R) :
    circleAverage (fun v : ℂ => Real.log (R / ‖u - v‖) + 1) z (3 * R / 2) =
      (Real.log R + 1) - (Real.log (3 * R / 2) + Real.posLog ((3 * R / 2)⁻¹ * ‖z - u‖)) := by
  have ht : (0 : ℝ) < 3 * R / 2 := by positivity
  have hEq : ∀ v : ℂ, v ≠ u →
      Real.log (R / ‖u - v‖) + 1 = (Real.log R + 1) - Real.log ‖v - u‖ := by
    intro v hv
    have huv : ‖u - v‖ ≠ 0 := by
      rw [norm_ne_zero_iff, sub_ne_zero]
      exact hv.symm
    rw [Real.log_div hR.ne' huv, norm_sub_rev]
    ring
  rw [circleAverage_congr_of_ne (f := fun v : ℂ => Real.log (R / ‖u - v‖) + 1)
    (g := fun v : ℂ => (Real.log R + 1) - Real.log ‖v - u‖) ht.ne' hEq]
  have hsub : (fun v : ℂ => (Real.log R + 1) - Real.log ‖v - u‖) =
      (fun _ : ℂ => Real.log R + 1) - (fun v : ℂ => Real.log ‖v - u‖) := rfl
  rw [hsub, circleAverage_sub (circleIntegrable_const _ _ _) (circleIntegrable_log_norm_sub_const _),
    circleAverage_const, circleAverage_log_norm_sub_const_eq_log_radius_add_posLog ht.ne']

/-- The circle average of the kernel is at most `log R + 1 - log (3R/2)`. -/
theorem circleAverage_kernel_le {z u : ℂ} {R : ℝ} (hR : 0 < R) :
    circleAverage (fun v : ℂ => Real.log (R / ‖u - v‖) + 1) z (3 * R / 2) ≤
      (Real.log R + 1) - Real.log (3 * R / 2) := by
  rw [circleAverage_kernel_eq hR]
  have h0 : 0 ≤ Real.posLog ((3 * R / 2)⁻¹ * ‖z - u‖) := by
    unfold Real.posLog
    exact le_max_left _ _
  linarith

/-- The integral of the kernel over `(0, 2π]` is at most `2π (log R + 1 - log (3R/2))`. -/
theorem integral_kernel_Ioc_le {z u : ℂ} {R : ℝ} (hR : 0 < R) :
    ∫ θ in Ioc 0 (2 * π), (Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1) ≤
      2 * π * ((Real.log R + 1) - Real.log (3 * R / 2)) := by
  have hav := circleAverage_kernel_le (z := z) (u := u) hR
  simp only [circleAverage_def, smul_eq_mul] at hav
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)] at hav
  have hpi : (0 : ℝ) < 2 * π := by positivity
  calc ∫ θ in Ioc 0 (2 * π), (Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1)
      = 2 * π * ((2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), (Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hpi.ne', one_mul]
    _ ≤ 2 * π * ((Real.log R + 1) - Real.log (3 * R / 2)) := mul_le_mul_of_nonneg_left hav hpi.le

/-- **Uniform bound on the absolute kernel over the annulus.** For `‖u - z‖ ≤ 2R`,
`∫_{(0,2π]} |K(u, circleMap θ)| dθ ≤ 2π (log R + 1 - log (3R/2) + 2 (log 4 - 1))`. -/
theorem integral_norm_kernel_le {z u : ℂ} {R : ℝ} (hR : 0 < R) (hu : ‖u - z‖ ≤ 2 * R) :
    ∫ θ in Ioc 0 (2 * π), ‖Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1‖ ≤
      2 * π * ((Real.log R + 1) - Real.log (3 * R / 2) + 2 * (Real.log 4 - 1)) := by
  have ht : (0 : ℝ) < 3 * R / 2 := by positivity
  have hint : IntegrableOn (fun θ : ℝ => Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1)
      (Ioc 0 (2 * π)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ 2 * π)).1
      (intervalIntegrable_kernel_slice (u := u) (z := z) (R := R) hR ht.ne')
  have hpt : ∀ θ ∈ Ioc (0 : ℝ) (2 * π),
      ‖Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1‖ ≤
        (Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1) + 2 * (Real.log 4 - 1) := by
    intro θ _
    have hz : ‖z - circleMap z (3 * R / 2) θ‖ = 3 * R / 2 := by
      rw [norm_circleMap_sub_center', abs_of_pos ht]
    have hdist : ‖u - circleMap z (3 * R / 2) θ‖ ≤ 4 * R := by
      have h1 : u - circleMap z (3 * R / 2) θ = (u - z) + (z - circleMap z (3 * R / 2) θ) := by ring
      have h2 := norm_add_le (u - z) (z - circleMap z (3 * R / 2) θ)
      rw [h1]
      linarith [h2, hu, hz]
    have hk := kernel_ge_neg hdist
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [one_le_log_four]
  have hconst : IntegrableOn (fun _ : ℝ => 2 * (Real.log 4 - 1)) (Ioc 0 (2 * π)) :=
    integrableOn_const measure_Ioc_lt_top.ne
  calc ∫ θ in Ioc 0 (2 * π), ‖Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1‖
      ≤ ∫ θ in Ioc 0 (2 * π),
          ((Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1) + 2 * (Real.log 4 - 1)) :=
        setIntegral_mono_on hint.norm (hint.add hconst) measurableSet_Ioc hpt
    _ = (∫ θ in Ioc 0 (2 * π), (Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1))
          + 2 * (Real.log 4 - 1) * (2 * π) := by
        rw [integral_add hint hconst, setIntegral_const,
          Real.volume_real_Ioc_of_le (show (0 : ℝ) ≤ 2 * π by positivity), smul_eq_mul]
        ring
    _ ≤ 2 * π * ((Real.log R + 1) - Real.log (3 * R / 2)) + 2 * (Real.log 4 - 1) * (2 * π) := by
        linarith [integral_kernel_Ioc_le (z := z) (u := u) hR]
    _ = 2 * π * ((Real.log R + 1) - Real.log (3 * R / 2) + 2 * (Real.log 4 - 1)) := by ring

end LatticeProb.CircleKernelBounds
