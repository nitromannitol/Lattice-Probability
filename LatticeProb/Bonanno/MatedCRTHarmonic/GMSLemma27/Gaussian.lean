/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSLemma27.Gaussian at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.GMCInterfaces
import LatticeProb.Bonanno.LQGMetric.Papers.DG.Lemma25Gauss

/-!
# Gaussian lower tail of circle averages (proof of [18] Lemma 2.8)

[18]: "For `z ∈ B_ρ(0)`, the random variable `h_δ(z)` is centered Gaussian with variance
`log δ⁻¹ + O_δ(1)`. Therefore, `P[e^{γ h_δ(z)} < δ^{p−ζ}] ≤ δ^{(p−ζ)²/(2γ²)}`." For a whole-plane GFF normalized by
`h_1(0) = 0` the variance is at most `log δ⁻¹` when `|z| + δ ≤ 1` (`variance_circleAvg_le`, from LQGDimension's
`gffCircleCov_formula`), and the Chernoff bound with LQGMetric's exponential moment `lintegral_exp_circleAvg` gives the
displayed estimate exactly (`measure_exp_circleAvg_lt_le`). Everything here is proved (SLE-free).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMSLemma27

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}

/-- `Var h_r(z) ≤ log r⁻¹` when `|z| + r ≤ 1`: the covariance `gffCircleCov r z r z` equals
`2 β_r(z) − log r` with `β_r(z) = ⨍_{∂B_r(z)} log max(|y|, 1) = 0`. -/
theorem gffCircleCov_self_le_neg_log {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ + r ≤ 1) :
    LQGDimension.gffCircleCov r z r z ≤ -Real.log r := by
  rw [LQGDimension.Osc37.gffCircleCov_formula hr, LQGDimension.Osc37.aAvg_self hr]
  have hb : LQGDimension.Osc37.betaAvg r z ≤ 0 := by
    apply Real.circleAverage_mono_on_of_le_circle (LQGDimension.Osc37.circleIntegrable_logMaxOne _ _)
    intro y hy
    rw [mem_sphere_iff_norm, abs_of_pos hr] at hy
    have hy1 : ‖y‖ ≤ 1 := by
      calc ‖y‖ = ‖(y - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ 1 := by rw [hy]; linarith
    rw [max_eq_right hy1, Real.log_one]
  linarith

/-- **Chernoff bound for a circle average.** For `r ∈ (0, 1)`, `|z| + r ≤ 1` and `a ≥ 0`,
`P[h_r(z) ≤ a log r] ≤ r^{a²/2}`. -/
theorem measure_circleAvg_le_mul_log_le (hG : LQGDimension.IsGFFCircleAverage H P) {r : ℝ}
    (hr : 0 < r) {z : ℂ} (hz : ‖z‖ + r ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    P {ω | H r z ω ≤ a * Real.log r} ≤ ENNReal.ofReal (r ^ (a ^ 2 / 2)) := by
  have hX : HasGaussianLaw (H r z) P :=
    (LQGDimension.SegLaw.isGaussianProcess_slice hG hr).hasGaussianLaw_eval z
  set f : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (-a * H r z ω)) with hf
  have hfm : AEMeasurable f P :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (Real.measurable_exp.comp_aemeasurable (hX.aemeasurable.const_mul (-a)))
  set t : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-a * (a * Real.log r))) with ht
  have hsub : {ω | H r z ω ≤ a * Real.log r} ⊆ {ω | t ≤ f ω} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith))
  have hmark := mul_meas_ge_le_lintegral₀ hfm t
  have hmom : ∫⁻ ω, f ω ∂P =
      ENNReal.ofReal (Real.exp (LQGDimension.gffCircleCov r z r z * (-a) ^ 2 / 2)) :=
    LQGMetric.DG.lintegral_exp_circleAvg hG hr z (-a)
  have ht0 : t ≠ 0 := by rw [ht]; exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have htt : t ≠ ⊤ := ENNReal.ofReal_ne_top
  have h1 : P {ω | H r z ω ≤ a * Real.log r} ≤
      ENNReal.ofReal (Real.exp (LQGDimension.gffCircleCov r z r z * (-a) ^ 2 / 2)) / t := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl ht0) (Or.inl htt), mul_comm, ← hmom]
    calc t * P {ω | H r z ω ≤ a * Real.log r} ≤ t * P {ω | t ≤ f ω} := by
          gcongr
      _ ≤ ∫⁻ ω, f ω ∂P := hmark
  refine h1.trans ?_
  rw [ht, ← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub,
    Real.rpow_def_of_pos hr]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hV := gffCircleCov_self_le_neg_log hr hz
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  have : LQGDimension.gffCircleCov r z r z * (-a) ^ 2 / 2 ≤ -Real.log r * a ^ 2 / 2 := by
    rw [neg_sq]
    have := mul_le_mul_of_nonneg_right hV ha2
    linarith
  nlinarith

/-- **[18] (proof of Lemma 2.8, `[18]`).** For `γ > 0`, `θ ≥ 0`, `r ∈ (0, 1)` and `|z| + r ≤ 1`,
`P[e^{γ h_r(z)} < r^θ] ≤ r^{θ²/(2γ²)}`. -/
theorem measure_exp_circleAvg_lt_le (hG : LQGDimension.IsGFFCircleAverage H P) {γ : ℝ} (hγ : 0 < γ)
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ + r ≤ 1) {θ : ℝ} (hθ : 0 ≤ θ) :
    P {ω | Real.exp (γ * H r z ω) < r ^ θ} ≤ ENNReal.ofReal (r ^ (θ ^ 2 / (2 * γ ^ 2))) := by
  have hsub : {ω | Real.exp (γ * H r z ω) < r ^ θ} ⊆ {ω | H r z ω ≤ θ / γ * Real.log r} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    rw [Real.rpow_def_of_pos hr, Real.exp_lt_exp] at hω
    rw [div_mul_eq_mul_div, le_div_iff₀ hγ]
    nlinarith
  refine (measure_mono hsub).trans ((measure_circleAvg_le_mul_log_le hG hr hz
    (div_nonneg hθ hγ.le)).trans (le_of_eq ?_))
  congr 2
  field_simp

end MatedCRTHarmonic.GMSLemma27
