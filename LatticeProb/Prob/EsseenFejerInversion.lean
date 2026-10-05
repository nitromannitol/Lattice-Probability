/- # Esseen's smoothing inequality: Fejér inversion

Let `μ`, `γ` be probability measures on `ℝ` with finite first absolute moments, put
`Δ u = μ (Iic u) - γ (Iic u)` and `ψ t = φ_μ t - φ_γ t`, where `φ = charFun`.  Smoothing `Δ` with
the Fejér kernel `k_T` and writing `k_T` as the Fourier integral of the triangle gives, after
Fubini and the Fourier transform of `Δ` (`∫ Δ u e^{itu} du = (φ_γ t - φ_μ t) / (i t)`),
`∫ Δ (x - w) k_T w dw = (1 / 2π) ∫_{-T}^{T} (1 - |t| / T) e^{-itx} (φ_γ t - φ_μ t) / (i t) dt`.
Bounding the triangle by one yields
`|∫ Δ (x - w) k_T w dw| ≤ (1 / 2π) ∫_{-T}^{T} ‖ψ t‖ / |t| dt`.

* `LatticeProb.intervalIntegrable_norm_charFun_sub_div` — the integrand `‖ψ t‖ / |t|` is
  integrable on `[-T, T]`.
* `LatticeProb.abs_smoothed_cdf_sub_le` — the Fejér-smoothed difference of distribution functions
  is bounded by the Fourier side.
-/
import Mathlib
import LatticeProb.Prob.FejerKernel
import LatticeProb.Prob.CdfDifferenceFourier

open MeasureTheory ProbabilityTheory

namespace LatticeProb

section FejerInversion

variable {μ γ : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]

/-- The integrand `‖ψ t‖ / |t|` is integrable on `[-T, T]` (it is bounded by the first moments). -/
theorem intervalIntegrable_norm_charFun_sub_div
    (hμ : Integrable (fun x : ℝ => |x|) μ) (hγ : Integrable (fun x : ℝ => |x|) γ)
    {T : ℝ} (_hT : 0 < T) :
    IntervalIntegrable (fun t : ℝ => ‖charFun μ t - charFun γ t‖ / |t|) volume (-T) T := by
  set C : ℝ := (∫ x, |x| ∂μ) + ∫ x, |x| ∂γ with hC
  have hC0 : 0 ≤ C := add_nonneg (integral_nonneg fun x => abs_nonneg x)
    (integral_nonneg fun x => abs_nonneg x)
  refine (intervalIntegrable_const (c := C)).mono_fun' ?_ ?_
  · exact ((continuous_charFun.sub continuous_charFun).norm.measurable.div
      continuous_abs.measurable).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t => ?_
    have hnn : 0 ≤ ‖charFun μ t - charFun γ t‖ / |t| := by positivity
    simp only [Real.norm_eq_abs, abs_of_nonneg hnn]
    by_cases ht : t = 0
    · simp [ht, hC0]
    · have htpos : 0 < |t| := abs_pos.2 ht
      rw [div_le_iff₀ htpos, mul_comm]
      exact norm_charFun_sub_le hμ hγ t

/-- The modulus of the Fourier character `e^{-i a}` with real `a` is one. -/
lemma norm_exp_neg_ofReal_mul_I (a : ℝ) : ‖Complex.exp (-((a : ℂ) * Complex.I))‖ = 1 := by
  have h : -((a : ℂ) * Complex.I) = ((-a : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure γ] in
/-- Change of variable `w ↦ x - w` in a smoothing integral. -/
lemma integral_cdf_sub_comp_sub_mul (x : ℝ) (k : ℝ → ℝ) :
    ∫ w : ℝ, ((μ (Set.Iic (x - w))).toReal - (γ (Set.Iic (x - w))).toReal) * k w
      = ∫ u : ℝ, ((μ (Set.Iic u)).toReal - (γ (Set.Iic u)).toReal) * k (x - u) := by
  have h := integral_sub_left_eq_self
    (fun u : ℝ => ((μ (Set.Iic u)).toReal - (γ (Set.Iic u)).toReal) * k (x - u)) volume x
  simpa only [sub_sub_cancel] using h

/-- The integrand of the Fubini step is integrable on `ℝ × (-T, T]`. -/
lemma integrable_cdf_sub_fejer_prod (hμ : Integrable (fun x : ℝ => |x|) μ)
    (hγ : Integrable (fun x : ℝ => |x|) γ) {T : ℝ} (hT : 0 < T) (x : ℝ) :
    Integrable (fun q : ℝ × ℝ =>
      (((μ (Set.Iic q.1)).toReal - (γ (Set.Iic q.1)).toReal : ℝ) : ℂ) *
        (((1 - |q.2| / T : ℝ) : ℂ) * Complex.exp (-((q.2 * (x - q.1) : ℝ) * Complex.I))))
      (volume.prod (volume.restrict (Set.Ioc (-T) T))) := by
  have hΔ := integrable_cdf_sub hμ hγ
  have hg : Integrable (fun t : ℝ => 1 + |t| / T) (volume.restrict (Set.Ioc (-T) T)) :=
    (by fun_prop : Continuous fun t : ℝ => 1 + |t| / T).integrableOn_Ioc
  refine (hΔ.norm.mul_prod hg).mono' ?_ (Filter.Eventually.of_forall fun q => ?_)
  · have h1 : AEStronglyMeasurable (fun q : ℝ × ℝ =>
        (((μ (Set.Iic q.1)).toReal - (γ (Set.Iic q.1)).toReal : ℝ) : ℂ))
        (volume.prod (volume.restrict (Set.Ioc (-T) T))) :=
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hΔ.aestronglyMeasurable).comp_fst
    have h2 : Continuous fun q : ℝ × ℝ =>
        ((1 - |q.2| / T : ℝ) : ℂ) * Complex.exp (-((q.2 * (x - q.1) : ℝ) * Complex.I)) := by
      fun_prop
    exact h1.mul h2.aestronglyMeasurable
  · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, norm_exp_neg_ofReal_mul_I,
      mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h0 : 0 ≤ |q.2| / T := div_nonneg (abs_nonneg _) hT.le
    rw [abs_le]
    constructor <;> linarith

/-- The `u`-integral of the Fubini integrand: the Fourier transform of `Δ` times the triangle
weight and the character `e^{-itx}`. -/
lemma integral_cdf_sub_fejer_inner (hμ : Integrable (fun x : ℝ => |x|) μ)
    (hγ : Integrable (fun x : ℝ => |x|) γ) {T : ℝ} (x : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ∫ u : ℝ, (((μ (Set.Iic u)).toReal - (γ (Set.Iic u)).toReal : ℝ) : ℂ) *
        (((1 - |t| / T : ℝ) : ℂ) * Complex.exp (-((t * (x - u) : ℝ) * Complex.I)))
      = ((1 - |t| / T : ℝ) : ℂ) * Complex.exp (-((t * x : ℝ) * Complex.I)) *
        ((charFun γ t - charFun μ t) / ((t : ℂ) * Complex.I)) := by
  have h : ∀ u : ℝ, (((μ (Set.Iic u)).toReal - (γ (Set.Iic u)).toReal : ℝ) : ℂ) *
        (((1 - |t| / T : ℝ) : ℂ) * Complex.exp (-((t * (x - u) : ℝ) * Complex.I)))
      = ((1 - |t| / T : ℝ) : ℂ) * Complex.exp (-((t * x : ℝ) * Complex.I)) *
        ((((μ (Set.Iic u)).toReal - (γ (Set.Iic u)).toReal : ℝ) : ℂ) *
          Complex.exp (((t * u : ℝ) : ℂ) * Complex.I)) := by
    intro u
    have hexp : Complex.exp (-((t * (x - u) : ℝ) * Complex.I))
        = Complex.exp (-((t * x : ℝ) * Complex.I)) *
          Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  simp_rw [h]
  rw [integral_const_mul, integral_cdf_sub_mul_exp hμ hγ t ht]

/-- The Fejér-smoothed difference of distribution functions, as a complex number, is the
Fourier-side integral over `(-T, T]` of the triangle weight against
`e^{-itx} (φ_γ t - φ_μ t) / (i t)`. -/
lemma complex_smoothed_cdf_sub_eq (hμ : Integrable (fun x : ℝ => |x|) μ)
    (hγ : Integrable (fun x : ℝ => |x|) γ) {T : ℝ} (hT : 0 < T) (x : ℝ) :
    ((∫ w : ℝ, ((μ (Set.Iic (x - w))).toReal - (γ (Set.Iic (x - w))).toReal) * fejerKernel T w
        : ℝ) : ℂ)
      = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in Set.Ioc (-T) T,
        ((1 - |t| / T : ℝ) : ℂ) * Complex.exp (-((t * x : ℝ) * Complex.I)) *
          ((charFun γ t - charFun μ t) / ((t : ℂ) * Complex.I)) := by
  rw [integral_cdf_sub_comp_sub_mul x (fejerKernel T), ← integral_complex_ofReal]
  have h1 : ∀ u : ℝ,
      ((((μ (Set.Iic u)).toReal - (γ (Set.Iic u)).toReal) * fejerKernel T (x - u) : ℝ) : ℂ)
        = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in Set.Ioc (-T) T,
          (((μ (Set.Iic u)).toReal - (γ (Set.Iic u)).toReal : ℝ) : ℂ) *
            (((1 - |t| / T : ℝ) : ℂ) * Complex.exp (-((t * (x - u) : ℝ) * Complex.I))) := by
    intro u
    rw [Complex.ofReal_mul, fejerKernel_eq_integral_exp hT (x - u),
      intervalIntegral.integral_of_le (by linarith), integral_const_mul]
    ring
  simp_rw [h1]
  rw [integral_const_mul]
  congr 1
  have hswap : ∫ u : ℝ, ∫ t in Set.Ioc (-T) T,
        (((μ (Set.Iic u)).toReal - (γ (Set.Iic u)).toReal : ℝ) : ℂ) *
          (((1 - |t| / T : ℝ) : ℂ) * Complex.exp (-((t * (x - u) : ℝ) * Complex.I)))
      = ∫ t in Set.Ioc (-T) T, ∫ u : ℝ,
        (((μ (Set.Iic u)).toReal - (γ (Set.Iic u)).toReal : ℝ) : ℂ) *
          (((1 - |t| / T : ℝ) : ℂ) * Complex.exp (-((t * (x - u) : ℝ) * Complex.I))) :=
    integral_integral_swap (integrable_cdf_sub_fejer_prod hμ hγ hT x)
  rw [hswap]
  refine integral_congr_ae ?_
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := Measure.ae_ne volume 0
  filter_upwards [ae_restrict_of_ae (s := Set.Ioc (-T) T) hne] with t ht
  exact integral_cdf_sub_fejer_inner hμ hγ x ht

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure γ] in
/-- Pointwise bound of the Fourier-side integrand by `‖ψ t‖ / |t|` for `t ∈ (-T, T]`. -/
lemma norm_fejer_integrand_le {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Ioc (-T) T) (x : ℝ) :
    ‖((1 - |t| / T : ℝ) : ℂ) * Complex.exp (-((t * x : ℝ) * Complex.I)) *
        ((charFun γ t - charFun μ t) / ((t : ℂ) * Complex.I))‖
      ≤ ‖charFun μ t - charFun γ t‖ / |t| := by
  have hle : |t| ≤ T := abs_le.2 ⟨ht.1.le, ht.2⟩
  have hdiv : |t| / T ≤ 1 := (div_le_one hT).2 hle
  have hdiv0 : 0 ≤ |t| / T := div_nonneg (abs_nonneg _) hT.le
  have hω0 : 0 ≤ 1 - |t| / T := by linarith
  have hq : 0 ≤ ‖charFun μ t - charFun γ t‖ / |t| := by positivity
  rw [norm_mul, norm_mul, Complex.norm_real, norm_exp_neg_ofReal_mul_I, norm_div, norm_mul,
    Complex.norm_real, Complex.norm_I, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hω0, norm_sub_rev (charFun γ t) (charFun μ t)]
  exact mul_le_of_le_one_left hq (by linarith)

/-- **Fejér inversion.**  The Fejér-smoothed difference of the distribution functions of two
probability measures with finite first absolute moments is bounded by the Fourier side
`(1 / 2π) ∫_{-T}^{T} ‖φ_μ t - φ_γ t‖ / |t| dt`. -/
theorem abs_smoothed_cdf_sub_le (hμ : Integrable (fun x : ℝ => |x|) μ)
    (hγ : Integrable (fun x : ℝ => |x|) γ) {T : ℝ} (hT : 0 < T) (x : ℝ) :
    |∫ w : ℝ, ((μ (Set.Iic (x - w))).toReal - (γ (Set.Iic (x - w))).toReal) * fejerKernel T w|
      ≤ (1 / (2 * Real.pi)) * ∫ t in (-T)..T, ‖charFun μ t - charFun γ t‖ / |t| := by
  have h := complex_smoothed_cdf_sub_eq hμ hγ hT x
  set I : ℝ := ∫ w : ℝ, ((μ (Set.Iic (x - w))).toReal - (γ (Set.Iic (x - w))).toReal) *
    fejerKernel T w with hI
  have habs : |I| = ‖(I : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [habs, h, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    intervalIntegral.integral_of_le (by linarith)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine norm_integral_le_of_norm_le ?_ ?_
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1
      (intervalIntegrable_norm_charFun_sub_div hμ hγ hT)
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun t ht => norm_fejer_integrand_le hT ht x

end FejerInversion

end LatticeProb
