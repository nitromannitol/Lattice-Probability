/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2Holding at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib

 








set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos

 
def expConvPow (r : ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | k + 1 => expConvPow r k ∗ expMeasure r

theorem isProbabilityMeasure_expConvPow {r : ℝ} (hr : 0 < r) :
    ∀ k, IsProbabilityMeasure (expConvPow r k)
  | 0 => by
    simp only [expConvPow]
    infer_instance
  | k + 1 => by
    have := isProbabilityMeasure_expConvPow hr k
    have := isProbabilityMeasure_expMeasure hr
    simp only [expConvPow]
    infer_instance

 
theorem gammaPDF_one_toReal {r : ℝ} (hr : 0 < r) (x : ℝ) :
    (gammaPDF 1 r x).toReal = Set.indicator (Set.Ici 0) (fun x => r * Real.exp (-(r * x))) x := by
  by_cases hx : 0 ≤ x
  · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hx)]
    have := exponentialPDF_of_nonneg (r := r) hx
    rw [exponentialPDF, exponentialPDFReal] at this
    rw [gammaPDF, this, ENNReal.toReal_ofReal (by positivity)]
  · rw [Set.indicator_of_notMem (by simpa using hx)]
    rw [gammaPDF_of_neg (lt_of_not_ge hx)]
    simp

theorem measurable_gammaPDF (a r : ℝ) : Measurable (gammaPDF a r) :=
  (measurable_gammaPDFReal a r).ennreal_ofReal

theorem ae_nonneg_expMeasure {r : ℝ} : ∀ᵐ x ∂(expMeasure r), 0 ≤ x := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
  rw [this, expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

theorem integral_cexp_mul_expMeasure {r : ℝ} (hr : 0 < r) (z : ℂ) (hz : z.re < r) :
    ∫ x, Complex.exp (z * x) ∂(expMeasure r) = r / (r - z) := by
  rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_gammaPDF 1 r)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp_rw [gammaPDF_one_toReal hr]
  have hind : ∀ x : ℝ, (Set.indicator (Set.Ici 0) (fun x => r * Real.exp (-(r * x))) x) •
      Complex.exp (z * x) = Set.indicator (Set.Ici 0)
        (fun x : ℝ => (r : ℂ) * Complex.exp ((z - r) * x)) x := by
    intro x
    by_cases hx : x ∈ Set.Ici (0 : ℝ)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Complex.real_smul]
      push_cast
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_smul]
  simp_rw [hind]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul, integral_exp_mul_complex_Ioi (by simpa using hz) 0]
  have hne : (r : ℂ) - z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hne' : z - (r : ℂ) ≠ 0 := by
    intro h; exact hne (by rw [← neg_sub, h, neg_zero])
  field_simp
  simp
  ring

theorem charFun_expMeasure {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    charFun (expMeasure r) θ = r / (r - θ * I) := by
  rw [charFun_apply_real]
  have hfun : (fun x : ℝ => Complex.exp (↑θ * ↑x * I)) =
      fun x : ℝ => Complex.exp ((↑θ * I) * ↑x) := by
    funext x; ring_nf
  rw [hfun]
  exact integral_cexp_mul_expMeasure hr ((θ : ℂ) * I) (by simpa using hr)

theorem charFun_expConvPow {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ∀ k : ℕ, charFun (expConvPow r k) θ = (r / (r - θ * I)) ^ k
  | 0 => by simp [expConvPow]
  | k + 1 => by
    have := isProbabilityMeasure_expConvPow hr k
    have := isProbabilityMeasure_expMeasure hr
    simp only [expConvPow]
    rw [charFun_conv, charFun_expConvPow hr θ k, charFun_expMeasure hr, pow_succ]

theorem lintegral_exp_neg_expMeasure {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-(s * x))) ∂(expMeasure r) = ENNReal.ofReal (r / (r + s)) := by
  have := isProbabilityMeasure_expMeasure hr
  have hint : Integrable (fun x => Real.exp (-(s * x))) (expMeasure r) := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (by fun_prop : Continuous fun x : ℝ => Real.exp (-(s * x))).aestronglyMeasurable ?_
    filter_upwards [ae_nonneg_expMeasure] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
  congr 1
  have hc := integral_cexp_mul_expMeasure hr (-(s : ℂ))
    (by rw [Complex.neg_re, Complex.ofReal_re]; linarith)
  have hfun : (fun x : ℝ => Complex.exp (-(s : ℂ) * x)) = fun x => ((Real.exp (-(s * x)) : ℝ) : ℂ) := by
    funext x
    rw [Complex.ofReal_exp]
    push_cast
    ring_nf
  rw [hfun, integral_complex_ofReal,
    show (r : ℂ) - -(s : ℂ) = ((r + s : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_div] at hc
  exact_mod_cast hc

theorem lintegral_exp_neg_expConvPow {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) :
    ∀ k : ℕ, ∫⁻ x, ENNReal.ofReal (Real.exp (-(s * x))) ∂(expConvPow r k) =
      ENNReal.ofReal ((r / (r + s)) ^ k)
  | 0 => by simp [expConvPow]
  | k + 1 => by
    have := isProbabilityMeasure_expConvPow hr k
    have := isProbabilityMeasure_expMeasure hr
    simp only [expConvPow]
    rw [Measure.lintegral_conv (by fun_prop)]
    have hsplit : ∀ x y : ℝ, ENNReal.ofReal (Real.exp (-(s * (x + y)))) =
        ENNReal.ofReal (Real.exp (-(s * x))) * ENNReal.ofReal (Real.exp (-(s * y))) := by
      intro x y
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    simp_rw [hsplit]
    simp_rw [lintegral_const_mul _ (by fun_prop : Measurable fun y : ℝ =>
      ENNReal.ofReal (Real.exp (-(s * y))))]
    rw [lintegral_exp_neg_expMeasure hr hs, lintegral_mul_const _ (by fun_prop),
      lintegral_exp_neg_expConvPow hr hs k, ← ENNReal.ofReal_mul (by positivity), pow_succ]

end SupercriticalLQGUniqueness.B2.QPos
