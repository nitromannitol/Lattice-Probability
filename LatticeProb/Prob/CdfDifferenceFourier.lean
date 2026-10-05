/- # The Fourier transform of a difference of distribution functions

For two probability measures `μ`, `γ` on `ℝ` with finite first absolute moment and
`Δ u = μ (Iic u) - γ (Iic u)` we show that `Δ` is integrable and
`∫ Δ(u) e^{itu} du = (φ_γ(t) - φ_μ(t)) / (i t)` for `t ≠ 0`, where `φ = charFun`.  We also
show that `φ_μ - φ_γ` vanishes linearly at `0`.
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace LatticeProb

section CharFunLinear

variable {μ γ : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]

/-- The function `x ↦ e^{i t x}` is integrable for a finite measure. -/
theorem integrable_cexp_real_mul_I {ν : Measure ℝ} [IsFiniteMeasure ν] (t : ℝ) :
    Integrable (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I)) ν := by
  refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x => ?_)
  rw [Complex.norm_exp_ofReal_mul_I]

/-- `‖φ_μ(t) - 1‖ ≤ |t| ∫ |x| dμ` for a probability measure with finite first moment. -/
theorem norm_charFun_sub_one_le (hμ : Integrable (fun x : ℝ => |x|) μ) (t : ℝ) :
    ‖charFun μ t - 1‖ ≤ |t| * ∫ x, |x| ∂μ := by
  have h1 : charFun μ t - 1 = ∫ x, (Complex.exp ((t * x : ℝ) * Complex.I) - 1) ∂μ := by
    rw [integral_sub (integrable_cexp_real_mul_I t) (integrable_const _), charFun_apply_real]
    simp
  rw [h1]
  calc ‖∫ x, (Complex.exp ((t * x : ℝ) * Complex.I) - 1) ∂μ‖
      ≤ ∫ x, |t| * |x| ∂μ := by
        refine norm_integral_le_of_norm_le (hμ.const_mul |t|)
          (Filter.Eventually.of_forall fun x => ?_)
        have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * x)
        rw [mul_comm Complex.I] at h
        rw [Real.norm_eq_abs, abs_mul] at h
        exact h
    _ = |t| * ∫ x, |x| ∂μ := integral_const_mul _ _

/-- The difference of characteristic functions vanishes linearly at `0`. -/
theorem norm_charFun_sub_le (hμ : Integrable (fun x : ℝ => |x|) μ)
    (hγ : Integrable (fun x : ℝ => |x|) γ) (t : ℝ) :
    ‖charFun μ t - charFun γ t‖ ≤ |t| * ((∫ x, |x| ∂μ) + ∫ x, |x| ∂γ) := by
  have h : charFun μ t - charFun γ t = (charFun μ t - 1) - (charFun γ t - 1) := by ring
  rw [h, mul_add]
  exact (norm_sub_le _ _).trans (add_le_add (norm_charFun_sub_one_le hμ t)
    (norm_charFun_sub_one_le hγ t))

end CharFunLinear

section Indicator

/-- The difference `1{x ≤ u} - 1{y ≤ u}` of two indicator functions in the variable `u`. -/
noncomputable def cdfIndDiff (x y u : ℝ) : ℝ :=
  (Set.Iic u).indicator (fun _ => (1 : ℝ)) x - (Set.Iic u).indicator (fun _ => (1 : ℝ)) y

/-- For `x ≤ y` the difference `1{x ≤ u} - 1{y ≤ u}` is the indicator of `[x, y)`. -/
theorem cdfIndDiff_of_le {x y : ℝ} (h : x ≤ y) (u : ℝ) :
    cdfIndDiff x y u = (Set.Ico x y).indicator (fun _ => (1 : ℝ)) u := by
  unfold cdfIndDiff
  by_cases h1 : x ≤ u <;> by_cases h2 : y ≤ u <;> simp [Set.indicator_apply, h1, h2]
  all_goals (exfalso; linarith)

/-- For `y < x` the difference `1{x ≤ u} - 1{y ≤ u}` is minus the indicator of `[y, x)`. -/
theorem cdfIndDiff_of_lt {x y : ℝ} (h : y < x) (u : ℝ) :
    cdfIndDiff x y u = -(Set.Ico y x).indicator (fun _ => (1 : ℝ)) u := by
  unfold cdfIndDiff
  by_cases h1 : x ≤ u <;> by_cases h2 : y ≤ u <;> simp [Set.indicator_apply, h1, h2]
  all_goals (exfalso; linarith)

/-- The integral of `u ↦ e^{i t u}` over `[x, y)` for `x ≤ y` and `t ≠ 0`. -/
theorem integral_Ico_cexp {x y : ℝ} (hxy : x ≤ y) {t : ℝ} (ht : t ≠ 0) :
    ∫ u in Set.Ico x y, Complex.exp (((t * u : ℝ) : ℂ) * Complex.I)
      = (Complex.exp (((t * y : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) / ((t : ℂ) * Complex.I) := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hxy]
  have hc : ((t : ℂ) * Complex.I) ≠ 0 := mul_ne_zero (by exact_mod_cast ht) Complex.I_ne_zero
  have h := integral_exp_mul_complex (a := x) (b := y) hc
  have e1 : ∀ u : ℝ, Complex.exp (((t * u : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((t : ℂ) * Complex.I) * (u : ℂ)) := fun u => by
    push_cast; ring_nf
  simp_rw [e1]
  rw [h]

/-- The Fourier integral of the difference of two indicators `1{x ≤ u} - 1{y ≤ u}`. -/
theorem integral_cdfIndDiff_mul_exp (x y : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ∫ u : ℝ, (cdfIndDiff x y u : ℂ) * Complex.exp (((t * u : ℝ) : ℂ) * Complex.I)
      = (Complex.exp (((t * y : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) / ((t : ℂ) * Complex.I) := by
  rcases le_or_gt x y with hxy | hxy
  · have h : ∀ u : ℝ, (cdfIndDiff x y u : ℂ) * Complex.exp (((t * u : ℝ) : ℂ) * Complex.I)
        = (Set.Ico x y).indicator
            (fun u : ℝ => Complex.exp (((t * u : ℝ) : ℂ) * Complex.I)) u := fun u => by
      rw [cdfIndDiff_of_le hxy]
      by_cases hu : u ∈ Set.Ico x y <;> simp [hu]
    simp_rw [h]
    rw [integral_indicator measurableSet_Ico]
    exact integral_Ico_cexp hxy ht
  · have h : ∀ u : ℝ, (cdfIndDiff x y u : ℂ) * Complex.exp (((t * u : ℝ) : ℂ) * Complex.I)
        = -(Set.Ico y x).indicator
            (fun u : ℝ => Complex.exp (((t * u : ℝ) : ℂ) * Complex.I)) u := fun u => by
      rw [cdfIndDiff_of_lt hxy]
      by_cases hu : u ∈ Set.Ico y x <;> simp [hu]
    simp_rw [h]
    rw [integral_neg, integral_indicator measurableSet_Ico, integral_Ico_cexp hxy.le ht]
    ring

/-- The integral of `|1{x ≤ u} - 1{y ≤ u}|` over `u` is `|x - y|`. -/
theorem integral_abs_cdfIndDiff (x y : ℝ) : ∫ u : ℝ, |cdfIndDiff x y u| = |x - y| := by
  rcases le_or_gt x y with hxy | hxy
  · have h : ∀ u : ℝ, |cdfIndDiff x y u| = (Set.Ico x y).indicator (fun _ => (1 : ℝ)) u :=
      fun u => by
      rw [cdfIndDiff_of_le hxy]
      by_cases hu : u ∈ Set.Ico x y <;> simp [hu]
    simp_rw [h]
    rw [integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico_of_le hxy,
      abs_of_nonpos (by linarith)]
    simp
  · have h : ∀ u : ℝ, |cdfIndDiff x y u| = (Set.Ico y x).indicator (fun _ => (1 : ℝ)) u :=
      fun u => by
      rw [cdfIndDiff_of_lt hxy]
      by_cases hu : u ∈ Set.Ico y x <;> simp [hu]
    simp_rw [h]
    rw [integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico_of_le hxy.le,
      abs_of_pos (by linarith)]
    simp

end Indicator

section Fubini

variable {μ γ : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]

/-- `cdfIndDiff` is jointly measurable in `(u, (x, y))`. -/
theorem measurable_cdfIndDiff :
    Measurable (fun q : ℝ × (ℝ × ℝ) => cdfIndDiff q.2.1 q.2.2 q.1) := by
  unfold cdfIndDiff
  simp only [Set.indicator_apply, Set.mem_Iic]
  refine Measurable.sub ?_ ?_ <;>
  exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) measurable_const
    measurable_const

/-- For fixed `x`, `y` the function `u ↦ 1{x ≤ u} - 1{y ≤ u}` is integrable. -/
theorem integrable_cdfIndDiff (x y : ℝ) : Integrable (fun u : ℝ => cdfIndDiff x y u) := by
  rcases le_or_gt x y with hxy | hxy
  · simp_rw [cdfIndDiff_of_le hxy]
    exact (integrable_indicator_iff measurableSet_Ico).2
      (integrableOn_const (by simp))
  · simp_rw [cdfIndDiff_of_lt hxy]
    exact ((integrable_indicator_iff measurableSet_Ico).2
      (integrableOn_const (by simp))).neg

/-- The function `(u, (x, y)) ↦ 1{x ≤ u} - 1{y ≤ u}` is integrable for the product of Lebesgue
measure and `μ ⊗ γ` when both measures have a finite first absolute moment. -/
theorem integrable_cdfIndDiff_prod (hμ : Integrable (fun x : ℝ => |x|) μ)
    (hγ : Integrable (fun x : ℝ => |x|) γ) :
    Integrable (fun q : ℝ × (ℝ × ℝ) => cdfIndDiff q.2.1 q.2.2 q.1)
      (volume.prod (μ.prod γ)) := by
  rw [integrable_prod_iff' measurable_cdfIndDiff.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun p => integrable_cdfIndDiff p.1 p.2, ?_⟩
  have h : ∀ p : ℝ × ℝ, ∫ u : ℝ, ‖cdfIndDiff p.1 p.2 u‖ = |p.1 - p.2| := fun p => by
    simp_rw [Real.norm_eq_abs]
    exact integral_abs_cdfIndDiff p.1 p.2
  simp_rw [h]
  refine ((hμ.comp_fst γ).add (hγ.comp_snd μ)).mono' (by fun_prop) ?_
  refine Filter.Eventually.of_forall fun p => ?_
  rw [Real.norm_eq_abs, abs_abs]
  exact abs_sub _ _

/-- The distribution function difference as an integral of `cdfIndDiff` against `μ ⊗ γ`. -/
theorem cdf_sub_eq_integral_cdfIndDiff (u : ℝ) :
    (μ (Set.Iic u)).toReal - (γ (Set.Iic u)).toReal
      = ∫ p : ℝ × ℝ, cdfIndDiff p.1 p.2 u ∂(μ.prod γ) := by
  have hI : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
      Integrable ((Set.Iic u).indicator (fun _ => (1 : ℝ))) ν := fun ν _ =>
    (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  unfold cdfIndDiff
  rw [integral_sub ((hI μ).comp_fst γ) ((hI γ).comp_snd μ),
    integral_fun_fst (fun x => (Set.Iic u).indicator (fun _ => (1 : ℝ)) x),
    integral_fun_snd (fun x => (Set.Iic u).indicator (fun _ => (1 : ℝ)) x),
    integral_indicator_const _ measurableSet_Iic, integral_indicator_const _ measurableSet_Iic]
  simp [measureReal_def]

/-- The difference of two distribution functions of probability measures with finite first
absolute moments is integrable. -/
theorem integrable_cdf_sub (hμ : Integrable (fun x : ℝ => |x|) μ)
    (hγ : Integrable (fun x : ℝ => |x|) γ) :
    Integrable (fun u : ℝ => (μ (Set.Iic u)).toReal - (γ (Set.Iic u)).toReal) := by
  have h := (integrable_cdfIndDiff_prod hμ hγ).integral_prod_left
  exact h.congr (Filter.Eventually.of_forall fun u => (cdf_sub_eq_integral_cdfIndDiff u).symm)

/-- **Fourier transform of a difference of distribution functions.**  For probability measures
`μ`, `γ` with finite first absolute moments and `t ≠ 0`,
`∫ (F_μ - F_γ)(u) e^{i t u} du = (φ_γ(t) - φ_μ(t)) / (i t)`. -/
theorem integral_cdf_sub_mul_exp (hμ : Integrable (fun x : ℝ => |x|) μ)
    (hγ : Integrable (fun x : ℝ => |x|) γ) (t : ℝ) (ht : t ≠ 0) :
    ∫ u : ℝ, (((μ (Set.Iic u)).toReal - (γ (Set.Iic u)).toReal : ℝ) : ℂ)
        * Complex.exp (((t * u : ℝ) : ℂ) * Complex.I)
      = (charFun γ t - charFun μ t) / ((t : ℂ) * Complex.I) := by
  set f : ℝ → ℝ × ℝ → ℂ := fun u p =>
    (cdfIndDiff p.1 p.2 u : ℂ) * Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) with hf
  have hint : Integrable (Function.uncurry f) (volume.prod (μ.prod γ)) := by
    refine (integrable_cdfIndDiff_prod hμ hγ).norm.mono' ?_
      (Filter.Eventually.of_forall fun q => ?_)
    · exact ((Complex.measurable_ofReal.comp measurable_cdfIndDiff).mul
        (by fun_prop)).aestronglyMeasurable
    · simp only [hf, Function.uncurry, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, le_refl]
  have hswap := integral_integral_swap hint
  have hL : ∀ u : ℝ, ∫ p : ℝ × ℝ, f u p ∂(μ.prod γ)
      = (((μ (Set.Iic u)).toReal - (γ (Set.Iic u)).toReal : ℝ) : ℂ)
        * Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) := fun u => by
    simp only [hf]
    rw [integral_mul_const, integral_complex_ofReal, ← cdf_sub_eq_integral_cdfIndDiff]
  have hR : ∀ p : ℝ × ℝ, ∫ u : ℝ, f u p
      = (Complex.exp (((t * p.2 : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((t * p.1 : ℝ) : ℂ) * Complex.I)) / ((t : ℂ) * Complex.I) :=
    fun p => integral_cdfIndDiff_mul_exp p.1 p.2 ht
  simp_rw [hL, hR] at hswap
  rw [hswap, integral_div, integral_sub ((integrable_cexp_real_mul_I t).comp_snd μ)
    ((integrable_cexp_real_mul_I t).comp_fst γ),
    integral_fun_snd (fun y : ℝ => Complex.exp (((t * y : ℝ) : ℂ) * Complex.I)),
    integral_fun_fst (fun x : ℝ => Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)),
    charFun_apply_real, charFun_apply_real]
  simp

end Fubini

end LatticeProb
