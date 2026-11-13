import Mathlib
import LatticeProb.LQG.DyadicDilationMeasure

/-!
# Rescaling of a local integral against the Liouville measure

Let `μ` be a measure on `ℂ`, `c > 0`, and suppose `μ.map (· / c) = K • ν`.  For a set `U ⊆ B(0, c)` and a
mark-dependent integrand `f(z, x)` the integral `∫_U f(z, x) dμ(z)` is `K` times the integral over the unit disk
of the rescaled integrand `dilatedIntegrand c U f` against `ν` (`lintegral_restrict_eq_mul_dilatedIntegrand`).
The deterministic weights produced by the rescaling and the Gaussian tilt combine into `max(1, |z|)^{γ²}` after the
change of variables `z = c w` (`lintegral_ball_weight_eq`).
-/

open MeasureTheory Metric
open scoped ENNReal

namespace LatticeProb.LQG.DyadicDilation

/-- The integrand `((w, x) ↦ 1_U (c w) f (c w, x))` of the rescaled local integral. -/
noncomputable def dilatedIntegrand {m : ℕ} (c : ℝ) (U : Set ℂ) (f : ℂ × (Fin m → ℝ) → ℝ≥0∞) :
    ℂ × (Fin m → ℝ) → ℝ≥0∞ :=
  {q : ℂ × (Fin m → ℝ) | (c : ℂ) * q.1 ∈ U}.indicator fun q => f ((c : ℂ) * q.1, q.2)

theorem measurable_dilatedIntegrand {m : ℕ} (c : ℝ) {U : Set ℂ} (hU : MeasurableSet U)
    {f : ℂ × (Fin m → ℝ) → ℝ≥0∞} (hf : Measurable f) : Measurable (dilatedIntegrand c U f) := by
  have h1 : Measurable fun q : ℂ × (Fin m → ℝ) => (c : ℂ) * q.1 := by fun_prop
  exact (hf.comp (h1.prodMk measurable_snd)).indicator (h1 hU)

/-- **Rescaling of the local integral.** -/
theorem lintegral_restrict_eq_mul_dilatedIntegrand {μ ν : Measure ℂ} {c : ℝ} (hc : 0 < c) {K : ℝ≥0∞}
    (hmap : μ.map (fun x => x / (c : ℂ)) = K • ν) {U : Set ℂ} (hU : MeasurableSet U)
    (hUc : U ⊆ ball (0 : ℂ) c) {m : ℕ} {f : ℂ × (Fin m → ℝ) → ℝ≥0∞} (hf : Measurable f)
    (x : Fin m → ℝ) :
    ∫⁻ z in U, f (z, x) ∂μ = K * ∫⁻ w in ball (0 : ℂ) 1, dilatedIntegrand c U f (w, x) ∂ν := by
  have hg : Measurable fun z => f (z, x) := hf.comp (measurable_id.prodMk measurable_const)
  have hfun : (fun w => dilatedIntegrand c U f (w, x)) =
      fun w => U.indicator (fun z => f (z, x)) ((c : ℂ) * w) := by
    funext w
    rfl
  have hsupp : Function.support (fun w => dilatedIntegrand c U f (w, x)) ⊆ ball (0 : ℂ) 1 := by
    intro w hw
    rw [Function.mem_support] at hw
    have hwU : (c : ℂ) * w ∈ U := by
      by_contra hn
      exact hw (by simp [dilatedIntegrand, hn])
    have h2 := hUc hwU
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le] at h2
    rw [mem_ball_zero_iff]
    by_contra hcon
    have := not_lt.1 hcon
    nlinarith
  rw [← lintegral_indicator hU, lintegral_eq_dilationFactor_mul_of_map_eq hc hmap (hg.indicator hU),
    setLIntegral_eq_of_support_subset hsupp, hfun]

/-- The deterministic weights combine into `c² max(1, |c w|)^{γ²}`. -/
theorem weight_eq {γ c : ℝ} (hc : 0 < c) (w : ℂ) :
    c ^ (2 + γ ^ 2 / 2) * Real.exp (γ ^ 2 * (-Real.log c⁻¹) / 2 + γ ^ 2 * Real.log (max c⁻¹ ‖w‖)) =
      c ^ 2 * max 1 ‖(c : ℂ) * w‖ ^ γ ^ 2 := by
  have hci : 0 < c⁻¹ := inv_pos.2 hc
  have ha : 0 < max c⁻¹ ‖w‖ := lt_max_of_lt_left hci
  have hca : max 1 ‖(c : ℂ) * w‖ = c * max c⁻¹ ‖w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le, mul_max_of_nonneg _ _ hc.le,
      mul_inv_cancel₀ hc.ne']
  have hc2 : c ^ 2 = Real.exp (2 * Real.log c) := by
    rw [show (2 : ℝ) * Real.log c = ((2 : ℕ) : ℝ) * Real.log c by norm_num, Real.exp_nat_mul,
      Real.exp_log hc]
  rw [hca, Real.rpow_def_of_pos hc, Real.rpow_def_of_pos (mul_pos hc ha), Real.log_mul hc.ne' ha.ne',
    Real.log_inv, hc2, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- **Change of variables `z = c w` for the combined weight.** -/
theorem lintegral_ball_weight_eq {γ c : ℝ} (hc : 0 < c) {U : Set ℂ} (hU : MeasurableSet U)
    (hUc : U ⊆ ball (0 : ℂ) c) (G : ℂ → ℝ≥0∞) :
    ∫⁻ w in ball (0 : ℂ) 1, ENNReal.ofReal (c ^ (2 + γ ^ 2 / 2)) *
        (ENNReal.ofReal (Real.exp (γ ^ 2 * (-Real.log c⁻¹) / 2 +
          γ ^ 2 * Real.log (max c⁻¹ ‖w‖))) * U.indicator G ((c : ℂ) * w)) =
      ∫⁻ z in U, ENNReal.ofReal (max 1 ‖z‖ ^ γ ^ 2) * G z := by
  set Φ : ℂ → ℝ≥0∞ := U.indicator (fun z => ENNReal.ofReal (max 1 ‖z‖ ^ γ ^ 2) * G z) with hΦ
  have hpt : ∀ w : ℂ, ENNReal.ofReal (c ^ (2 + γ ^ 2 / 2)) *
        (ENNReal.ofReal (Real.exp (γ ^ 2 * (-Real.log c⁻¹) / 2 + γ ^ 2 * Real.log (max c⁻¹ ‖w‖))) *
          U.indicator G ((c : ℂ) * w)) = ENNReal.ofReal (c ^ 2) * Φ ((c : ℂ) * w) := by
    intro w
    by_cases hw : (c : ℂ) * w ∈ U
    · simp only [hΦ, Set.indicator_of_mem hw]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), weight_eq hc w,
        ENNReal.ofReal_mul (by positivity), mul_assoc]
    · simp [hΦ, Set.indicator_of_notMem hw]
  have hsupp : Function.support (fun w : ℂ => ENNReal.ofReal (c ^ 2) * Φ ((c : ℂ) * w)) ⊆
      ball (0 : ℂ) 1 := by
    intro w hw
    rw [Function.mem_support] at hw
    have hwU : (c : ℂ) * w ∈ U := by
      by_contra hn
      exact hw (by simp [hΦ, hn])
    have h2 := hUc hwU
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le] at h2
    rw [mem_ball_zero_iff]
    by_contra hcon
    have := not_lt.1 hcon
    nlinarith
  have hcv : ∫⁻ w, Φ ((c : ℂ) * w) = ENNReal.ofReal ((c ^ 2)⁻¹) * ∫⁻ z, Φ z := by
    let e : ℂ ≃ᵐ ℂ := MeasurableEquiv.smul₀ c hc.ne'
    have hemb := e.measurableEmbedding
    have hmap := Measure.map_addHaar_smul (volume : Measure ℂ) hc.ne'
    simp only [Complex.finrank_real_complex] at hmap
    have h1 := hemb.lintegral_map (μ := (volume : Measure ℂ)) Φ
    have h2 : (e : ℂ → ℂ) = fun w => c • w := rfl
    rw [h2, hmap, lintegral_smul_measure, smul_eq_mul, abs_of_pos (by positivity)] at h1
    refine (lintegral_congr fun w => ?_).trans h1.symm
    show Φ ((c : ℂ) * w) = Φ (c • w)
    rw [Complex.real_smul]
  have hRHS : ∫⁻ z in U, ENNReal.ofReal (max 1 ‖z‖ ^ γ ^ 2) * G z = ∫⁻ z, Φ z :=
    (lintegral_indicator hU _).symm
  rw [setLIntegral_congr_fun measurableSet_ball (fun w _ => hpt w), hRHS,
    setLIntegral_eq_of_support_subset hsupp, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hcv,
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity),
    ENNReal.ofReal_one, one_mul]

end LatticeProb.LQG.DyadicDilation
