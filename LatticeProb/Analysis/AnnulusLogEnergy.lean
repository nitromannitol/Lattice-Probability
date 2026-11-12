import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Dirichlet energy of the capacitary potential of a round annulus

For `0 < s < r` and `c ∈ ℂ`, the function `u(z) = log(r / |z - c|) / log(r / s)` is the harmonic function on the
annulus `D = B_r(c) \ B̄_s(c)` equal to `1` on `∂B_s(c)` and to `0` on `∂B_r(c)` (the capacitary potential of the
condenser `(B̄_s(c), B_r(c))`). Its Dirichlet energy is the capacity of the condenser:
`∫_D |∇u|² = 2π / log(r / s)`.

## Main results

* `LatticeProb.exists_hasFDerivAt_log_norm_sub`: `z ↦ log |z - c|` is differentiable off `c`, with gradient of norm
  `|z - c|⁻¹`.
* `LatticeProb.norm_fderiv_log_div_norm_sub`: `|∇ (log(r / |· - c|) / L)(z)| = |L|⁻¹ |z - c|⁻¹` for `z ≠ c`.
* `LatticeProb.lintegral_Ioo_inv`: `∫_s^r ρ⁻¹ dρ = log(r / s)` as a lower Lebesgue integral.
* `LatticeProb.lintegral_annulus_inv_norm_sq`: `∫_D |z - c|⁻² dz = 2π log(r / s)` (polar coordinates).
* `LatticeProb.lintegral_annulus_norm_fderiv_log_div_sq`: `∫_D |∇u|² = 2π / log(r / s)`.
-/

open Metric MeasureTheory Set

namespace LatticeProb

/-- `z ↦ log |z - c|` is differentiable at every `z ≠ c`, and its gradient has norm `|z - c|⁻¹`. -/
theorem exists_hasFDerivAt_log_norm_sub (c z : ℂ) (hz : z ≠ c) :
    ∃ D : ℂ →L[ℝ] ℝ, HasFDerivAt (fun w : ℂ => Real.log ‖w - c‖) D z ∧ ‖D‖ = ‖z - c‖⁻¹ := by
  have hzc : z - c ≠ 0 := sub_ne_zero.2 hz
  have hn : 0 < ‖z - c‖ := norm_pos_iff.2 hzc
  have h1 := HasFDerivAt.comp (g := fun x : ℂ => ‖x‖ ^ 2) (f := fun w : ℂ => w - c) z
    (hasStrictFDerivAt_norm_sq (z - c)).hasFDerivAt ((hasFDerivAt_id z).sub_const c)
  have h2 := h1.log (show ‖z - c‖ ^ 2 ≠ 0 from pow_ne_zero 2 hn.ne')
  have hfun : (fun w : ℂ => Real.log ‖w - c‖) = fun w => (1 / 2 : ℝ) * Real.log (‖w - c‖ ^ 2) := by
    funext w
    rw [Real.log_pow]
    push_cast
    ring
  refine ⟨(1 / 2 : ℝ) • ((‖z - c‖ ^ 2)⁻¹ • (2 • innerSL ℝ (z - c)).comp (ContinuousLinearMap.id ℝ ℂ)), ?_, ?_⟩
  · rw [hfun]
    exact h2.const_mul (1 / 2 : ℝ)
  · have h2n : ‖(2 • innerSL ℝ (z - c) : ℂ →L[ℝ] ℝ)‖ = 2 * ‖z - c‖ := by
      rw [two_nsmul, ← two_smul ℝ, norm_smul, innerSL_apply_norm]; norm_num
    rw [ContinuousLinearMap.comp_id, norm_smul, norm_smul, h2n]
    simp only [Real.norm_eq_abs]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_pos (by positivity)]
    field_simp

/-- The gradient of `z ↦ log(r / |z - c|) / L` at `z ≠ c` has norm `|L|⁻¹ |z - c|⁻¹`. -/
theorem norm_fderiv_log_div_norm_sub (c : ℂ) {z : ℂ} (hz : z ≠ c) {r : ℝ} (hr : 0 < r) (L : ℝ) :
    ‖fderiv ℝ (fun w : ℂ => Real.log (r / ‖w - c‖) / L) z‖ = |L|⁻¹ * ‖z - c‖⁻¹ := by
  obtain ⟨D, hD, hDn⟩ := exists_hasFDerivAt_log_norm_sub c z hz
  have hv : HasFDerivAt (fun w : ℂ => (Real.log r - Real.log ‖w - c‖) * L⁻¹) (L⁻¹ • -D) z :=
    (hD.const_sub (Real.log r)).mul_const L⁻¹
  have hev : (fun w : ℂ => Real.log (r / ‖w - c‖) / L) =ᶠ[nhds z]
      fun w : ℂ => (Real.log r - Real.log ‖w - c‖) * L⁻¹ := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    rw [Real.log_div hr.ne' (norm_ne_zero_iff.2 (sub_ne_zero.2 hw)), div_eq_mul_inv]
  rw [(hv.congr_of_eventuallyEq hev).fderiv, norm_smul, norm_neg, hDn, Real.norm_eq_abs, abs_inv]

/-- `∫_s^r ρ⁻¹ dρ = log(r / s)` for `0 < s ≤ r`, as a lower Lebesgue integral over `(s, r)`. -/
theorem lintegral_Ioo_inv {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) :
    ∫⁻ ρ in Ioo s r, ENNReal.ofReal ρ⁻¹ = ENNReal.ofReal (Real.log (r / s)) := by
  have hint : IntegrableOn (fun ρ : ℝ => ρ⁻¹) (Ioo s r) :=
    ((continuousOn_inv₀.mono fun x hx => (hs.trans_le hx.1).ne').integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioo fun ρ hρ => (inv_pos.2 (hs.trans hρ.1)).le)]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hsr,
    integral_inv_of_pos hs (hs.trans_le hsr)]

/-- The radial integral `∫_{B_r(0) \ B̄_s(0)} |z|⁻² dz = 2π log(r / s)` in polar coordinates. -/
theorem lintegral_indicator_annulus_inv_norm_sq {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) :
    ∫⁻ z : ℂ, (ball (0 : ℂ) r \ closedBall 0 s).indicator (fun x => ENNReal.ofReal (‖x‖ ^ 2)⁻¹) z =
      ENNReal.ofReal (2 * Real.pi * Real.log (r / s)) := by
  rw [← Complex.lintegral_comp_polarCoord_symm, show polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi from rfl]
  have hpt : EqOn (fun p : ℝ × ℝ => ENNReal.ofReal p.1 •
      (ball (0 : ℂ) r \ closedBall 0 s).indicator (fun x => ENNReal.ofReal (‖x‖ ^ 2)⁻¹)
        (Complex.polarCoord.symm p))
      (fun p : ℝ × ℝ => (Ioo s r).indicator (fun ρ => ENNReal.ofReal ρ⁻¹) p.1) (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) := by
    rintro ⟨ρ, θ⟩ ⟨hρ, -⟩
    simp only [mem_Ioi] at hρ
    have hn : ‖Complex.polarCoord.symm (ρ, θ)‖ = ρ := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hρ]
    by_cases h : ρ ∈ Ioo s r
    · have hm : Complex.polarCoord.symm (ρ, θ) ∈ ball (0 : ℂ) r \ closedBall 0 s := by
        simp only [mem_sdiff, mem_ball, mem_closedBall, dist_zero_right, hn, not_le]
        exact ⟨h.2, h.1⟩
      simp only
      rw [indicator_of_mem hm, indicator_of_mem h, hn, smul_eq_mul, ← ENNReal.ofReal_mul hρ.le]
      congr 1
      field_simp
    · have hm : Complex.polarCoord.symm (ρ, θ) ∉ ball (0 : ℂ) r \ closedBall 0 s := by
        simp only [mem_sdiff, mem_ball, mem_closedBall, dist_zero_right, hn, not_le]
        exact fun h' => h ⟨h'.2, h'.1⟩
      simp only
      rw [indicator_of_notMem hm, indicator_of_notMem h, smul_zero]
  rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hpt, Measure.volume_eq_prod,
    ← Measure.prod_restrict]
  have hmeas : Measurable fun ρ : ℝ => (Ioo s r).indicator (fun ρ => ENNReal.ofReal ρ⁻¹) ρ :=
    (ENNReal.measurable_ofReal.comp measurable_inv).indicator measurableSet_Ioo
  rw [lintegral_prod (fun p : ℝ × ℝ => (Ioo s r).indicator (fun ρ => ENNReal.ofReal ρ⁻¹) p.1)
    (hmeas.comp measurable_fst).aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
  rw [lintegral_mul_const _ hmeas, lintegral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.2 (show Ioo s r ⊆ Ioi (0 : ℝ) from fun ρ hρ => hs.trans hρ.1), lintegral_Ioo_inv hs hsr,
    ← ENNReal.ofReal_mul (Real.log_nonneg ((one_le_div hs).2 hsr))]
  congr 1
  ring

/-- **Energy integral of the annulus**: `∫_{B_r(c) \ B̄_s(c)} |z - c|⁻² dz = 2π log(r / s)` for `0 < s ≤ r`. -/
theorem lintegral_annulus_inv_norm_sq (c : ℂ) {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) :
    ∫⁻ z in ball c r \ closedBall c s, ENNReal.ofReal (‖z - c‖ ^ 2)⁻¹ =
      ENNReal.ofReal (2 * Real.pi * Real.log (r / s)) := by
  rw [← lintegral_indicator (measurableSet_ball.diff measurableSet_closedBall)]
  have hind : (ball c r \ closedBall c s).indicator (fun z => ENNReal.ofReal (‖z - c‖ ^ 2)⁻¹) =
      fun z => (ball (0 : ℂ) r \ closedBall 0 s).indicator (fun x => ENNReal.ofReal (‖x‖ ^ 2)⁻¹) (z - c) := by
    funext z
    have hiff : z ∈ ball c r \ closedBall c s ↔ z - c ∈ ball (0 : ℂ) r \ closedBall 0 s := by
      simp only [mem_sdiff, mem_ball, mem_closedBall, dist_eq_norm, sub_zero]
    by_cases h : z ∈ ball c r \ closedBall c s
    · rw [indicator_of_mem h, indicator_of_mem (hiff.1 h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (hiff.not.1 h)]
  rw [hind, lintegral_sub_right_eq_self
    (fun x => (ball (0 : ℂ) r \ closedBall 0 s).indicator (fun x => ENNReal.ofReal (‖x‖ ^ 2)⁻¹) x) c,
    lintegral_indicator_annulus_inv_norm_sq hs hsr]

/-- **Dirichlet energy of the capacitary potential of a round annulus**: for `0 < s < r`, the function
`u(z) = log(r / |z - c|) / log(r / s)` has `∫_{B_r(c) \ B̄_s(c)} |∇u|² = 2π / log(r / s)`. -/
theorem lintegral_annulus_norm_fderiv_log_div_sq (c : ℂ) {s r : ℝ} (hs : 0 < s) (hsr : s < r) :
    ∫⁻ z in ball c r \ closedBall c s,
        ENNReal.ofReal (‖fderiv ℝ (fun w : ℂ => Real.log (r / ‖w - c‖) / Real.log (r / s)) z‖ ^ 2) =
      ENNReal.ofReal (2 * Real.pi / Real.log (r / s)) := by
  have hr : 0 < r := hs.trans hsr
  have hL : 0 < Real.log (r / s) := Real.log_pos ((one_lt_div hs).2 hsr)
  have hpt : EqOn
      (fun z => ENNReal.ofReal (‖fderiv ℝ (fun w : ℂ => Real.log (r / ‖w - c‖) / Real.log (r / s)) z‖ ^ 2))
      (fun z => ENNReal.ofReal ((Real.log (r / s) ^ 2)⁻¹) * ENNReal.ofReal (‖z - c‖ ^ 2)⁻¹)
      (ball c r \ closedBall c s) := by
    intro z hz
    have hzc : z ≠ c := by
      rintro rfl
      exact hz.2 (mem_closedBall_self hs.le)
    simp only
    rw [norm_fderiv_log_div_norm_sub c hzc hr, ← ENNReal.ofReal_mul (by positivity), abs_of_pos hL]
    congr 1
    rw [mul_pow, inv_pow, inv_pow]
  rw [setLIntegral_congr_fun (measurableSet_ball.diff measurableSet_closedBall) hpt,
    lintegral_const_mul _ (Measurable.ennreal_ofReal (by fun_prop : Measurable fun z : ℂ => (‖z - c‖ ^ 2)⁻¹)),
    lintegral_annulus_inv_norm_sq c hs hsr.le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
