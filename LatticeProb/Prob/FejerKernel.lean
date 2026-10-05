/- # The Fejér kernel

The Fejér kernel `k_T(x) = (1 - cos (T x)) / (π T x²)` is defined through its cosine-integral
representation `(1 / π) ∫_0^T (1 - t / T) cos (t x) dt`, which is meaningful and continuous at
`x = 0`.  Its Fourier transform is the triangle `max 0 (1 - |t| / T)`.  This file proves the
closed form, nonnegativity, the two-sided bounds, evenness, continuity, integrability, total mass
one, the tail bound `∫_{|w| > h} k_T ≤ 4 / (π T h)`, and the Fourier representation.
-/
import Mathlib

open MeasureTheory Set
open scoped FourierTransform

namespace LatticeProb

/-- Fejér kernel, defined by its cosine-integral representation. -/
noncomputable def fejerKernel (T x : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ t in (0 : ℝ)..T, (1 - t / T) * Real.cos (t * x)

/-- Closed form of the cosine integral for `x ≠ 0`. -/
lemma integral_fejer_cos {T : ℝ} (hT : 0 < T) {x : ℝ} (hx : x ≠ 0) :
    ∫ t in (0 : ℝ)..T, (1 - t / T) * Real.cos (t * x) = (1 - Real.cos (T * x)) / (T * x ^ 2) := by
  have hT0 : T ≠ 0 := hT.ne'
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt
        (fun t : ℝ => (1 - t / T) * (Real.sin (t * x) / x) - Real.cos (t * x) / (T * x ^ 2))
        ((1 - t / T) * Real.cos (t * x)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => 1 - t / T) (-(1 / T)) t := by
      simpa using ((hasDerivAt_id t).div_const T).const_sub 1
    have h2 : HasDerivAt (fun t : ℝ => Real.sin (t * x) / x) (Real.cos (t * x)) t := by
      have := ((hasDerivAt_id' t).mul_const x).sin.div_const x
      refine this.congr_deriv ?_
      field_simp
    have h3 : HasDerivAt (fun t : ℝ => Real.cos (t * x) / (T * x ^ 2))
        (-(Real.sin (t * x) * x) / (T * x ^ 2)) t := by
      have := ((hasDerivAt_id' t).mul_const x).cos.div_const (T * x ^ 2)
      refine this.congr_deriv ?_
      ring
    refine ((h1.mul h2).sub h3).congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable (fun t : ℝ => (1 - t / T) * Real.cos (t * x))
      MeasureTheory.volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [zero_mul, Real.sin_zero, zero_div, Real.cos_zero, div_self hT0, sub_self, mul_zero]
  field_simp
  ring

/-- Closed form of the Fejér kernel away from the origin. -/
theorem fejerKernel_eq {T : ℝ} (hT : 0 < T) {x : ℝ} (hx : x ≠ 0) :
    fejerKernel T x = (1 - Real.cos (T * x)) / (Real.pi * T * x ^ 2) := by
  unfold fejerKernel
  rw [integral_fejer_cos hT hx]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hT0 : T ≠ 0 := hT.ne'
  field_simp

/-- The Fejér kernel at the origin. -/
theorem fejerKernel_zero {T : ℝ} (hT : 0 < T) : fejerKernel T 0 = T / (2 * Real.pi) := by
  unfold fejerKernel
  have hT0 : T ≠ 0 := hT.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h : ∫ t in (0 : ℝ)..T, (1 - t / T) * Real.cos (t * 0) = T / 2 := by
    simp only [mul_zero, Real.cos_zero, mul_one]
    rw [intervalIntegral.integral_sub (by simp) (by simp)]
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    rw [intervalIntegral.integral_div, integral_id]
    field_simp
    ring
  rw [h]
  field_simp

/-- The Fejér kernel is nonnegative. -/
theorem fejerKernel_nonneg {T : ℝ} (hT : 0 < T) (x : ℝ) : 0 ≤ fejerKernel T x := by
  by_cases hx : x = 0
  · subst hx
    rw [fejerKernel_zero hT]
    positivity
  · rw [fejerKernel_eq hT hx]
    have := Real.cos_le_one (T * x)
    have hpos : 0 < Real.pi * T * x ^ 2 := by positivity
    exact div_nonneg (by linarith) hpos.le

/-- The Fejér kernel is bounded by its value at the origin. -/
theorem fejerKernel_le {T : ℝ} (hT : 0 < T) (x : ℝ) : fejerKernel T x ≤ T / (2 * Real.pi) := by
  by_cases hx : x = 0
  · subst hx
    rw [fejerKernel_zero hT]
  · rw [fejerKernel_eq hT hx]
    have h1 := Real.one_sub_sq_div_two_le_cos (x := T * x)
    have hpos : 0 < Real.pi * T * x ^ 2 := by positivity
    rw [div_le_div_iff₀ hpos (by positivity)]
    have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith [mul_pos hpi hT, sq_nonneg x, mul_nonneg (mul_pos hpi hT).le (sq_nonneg x)]

/-- The Fejér kernel decays quadratically. -/
theorem fejerKernel_le_sq {T : ℝ} (hT : 0 < T) {x : ℝ} (hx : x ≠ 0) :
    fejerKernel T x ≤ 2 / (Real.pi * T * x ^ 2) := by
  rw [fejerKernel_eq hT hx]
  have := Real.neg_one_le_cos (T * x)
  have hpos : 0 < Real.pi * T * x ^ 2 := by positivity
  exact div_le_div_of_nonneg_right (by linarith) hpos.le

/-- The Fejér kernel is even. -/
theorem fejerKernel_neg {T : ℝ} (_hT : 0 < T) (x : ℝ) :
    fejerKernel T (-x) = fejerKernel T x := by
  unfold fejerKernel
  simp only [mul_neg, Real.cos_neg]

/-- The Fejér kernel is continuous. -/
theorem continuous_fejerKernel {T : ℝ} (_hT : 0 < T) : Continuous (fejerKernel T) := by
  unfold fejerKernel
  refine continuous_const.mul ?_
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x t : ℝ => (1 - t / T) * Real.cos (t * x)) (by fun_prop) 0 T

/-- The Fejér kernel times `1 + x²` is bounded. -/
lemma fejerKernel_mul_le {T : ℝ} (hT : 0 < T) (x : ℝ) :
    fejerKernel T x * (1 + x ^ 2) ≤ T / Real.pi + 4 / (Real.pi * T) := by
  have hpi := Real.pi_pos
  have hk0 := fejerKernel_nonneg hT x
  have hC : 0 ≤ 4 / (Real.pi * T) := by positivity
  by_cases h : x ^ 2 ≤ 1
  · have h1 := fejerKernel_le hT x
    calc fejerKernel T x * (1 + x ^ 2) ≤ T / (2 * Real.pi) * 2 := by
          apply mul_le_mul h1 (by linarith) (by positivity) (by positivity)
      _ = T / Real.pi := by field_simp
      _ ≤ _ := by linarith
  · have hx : x ≠ 0 := by
      rintro rfl
      simp at h
    have h1 := fejerKernel_le_sq hT hx
    have h2 : 1 + x ^ 2 ≤ 2 * x ^ 2 := by linarith [not_le.mp h]
    calc fejerKernel T x * (1 + x ^ 2) ≤ 2 / (Real.pi * T * x ^ 2) * (2 * x ^ 2) := by
          apply mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 4 / (Real.pi * T) := by field_simp; ring
      _ ≤ _ := by linarith [show 0 ≤ T / Real.pi by positivity]

/-- The Fejér kernel is integrable. -/
theorem integrable_fejerKernel {T : ℝ} (hT : 0 < T) : Integrable (fejerKernel T) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (T / Real.pi + 4 / (Real.pi * T)))
    (continuous_fejerKernel hT).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (fejerKernel_nonneg hT x), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact fejerKernel_mul_le hT x

/-- The right half of the tail mass. -/
lemma integral_Ioi_fejerKernel_le {T : ℝ} (hT : 0 < T) {h : ℝ} (hh : 0 < h) :
    ∫ w in Ioi h, fejerKernel T w ≤ 2 / (Real.pi * T * h) := by
  have hpi := Real.pi_pos
  have hint : IntegrableOn (fun w : ℝ => 2 / (Real.pi * T) * w ^ (-2 : ℝ)) (Ioi h) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hh).const_mul _
  have hmono : ∫ w in Ioi h, fejerKernel T w ≤
      ∫ w in Ioi h, 2 / (Real.pi * T) * w ^ (-2 : ℝ) := by
    refine setIntegral_mono_on (integrable_fejerKernel hT).integrableOn hint measurableSet_Ioi ?_
    intro w hw
    have hw0 : 0 < w := hh.trans hw
    have := fejerKernel_le_sq hT hw0.ne'
    calc fejerKernel T w ≤ 2 / (Real.pi * T * w ^ 2) := this
      _ = 2 / (Real.pi * T) * w ^ (-2 : ℝ) := by
          rw [Real.rpow_neg hw0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
          field_simp
  refine hmono.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hh]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  field_simp

/-- Tail mass: `∫_{|w| > h} k_T ≤ 4 / (π T h)`. -/
theorem fejerKernel_tail {T : ℝ} (hT : 0 < T) {h : ℝ} (hh : 0 < h) :
    ∫ w in {w : ℝ | h < |w|}, fejerKernel T w ≤ 4 / (Real.pi * T * h) := by
  have hpi := Real.pi_pos
  have hset : {w : ℝ | h < |w|} = Iio (-h) ∪ Ioi h := by
    ext w
    simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Ioi]
    constructor
    · intro hw
      rcases le_or_gt 0 w with h0 | h0
      · right
        rwa [abs_of_nonneg h0] at hw
      · left
        rw [abs_of_neg h0] at hw
        linarith
    · rintro (hw | hw)
      · exact lt_of_lt_of_le (by linarith) (neg_le_abs w)
      · exact lt_of_lt_of_le hw (le_abs_self w)
  have hdisj : Disjoint (Iio (-h)) (Ioi h) := by
    rw [Set.disjoint_left]
    intro w hw1 hw2
    rw [mem_Iio] at hw1
    rw [mem_Ioi] at hw2
    linarith
  have hleft : ∫ w in Iio (-h), fejerKernel T w = ∫ w in Ioi h, fejerKernel T w := by
    rw [← integral_Iic_eq_integral_Iio]
    rw [setIntegral_congr_fun measurableSet_Iic
      (fun w _ => (fejerKernel_neg hT w).symm : EqOn (fejerKernel T) (fun w => fejerKernel T (-w))
        (Iic (-h))), integral_comp_neg_Iic, neg_neg]
  rw [hset, setIntegral_union hdisj measurableSet_Ioi (integrable_fejerKernel hT).integrableOn
    (integrable_fejerKernel hT).integrableOn, hleft]
  have := integral_Ioi_fejerKernel_le hT hh
  calc (∫ w in Ioi h, fejerKernel T w) + ∫ w in Ioi h, fejerKernel T w
      ≤ 2 / (Real.pi * T * h) + 2 / (Real.pi * T * h) := add_le_add this this
    _ = 4 / (Real.pi * T * h) := by ring

/-- Pointwise identity for the integrand of the Fourier representation. -/
lemma fejer_exp_pair {T : ℝ} (x t : ℝ) :
    ((1 - |-t| / T : ℝ) : ℂ) * Complex.exp (-(((-t) * x : ℝ) * Complex.I)) +
      ((1 - |t| / T : ℝ) : ℂ) * Complex.exp (-((t * x : ℝ) * Complex.I)) =
      (((1 - |t| / T) * (2 * Real.cos (t * x)) : ℝ) : ℂ) := by
  have h1 : -((((-t) * x : ℝ) : ℂ) * Complex.I) = ((t * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have h2 : -(((t * x : ℝ) : ℂ) * Complex.I) = -((t * x : ℝ) : ℂ) * Complex.I := by ring
  rw [abs_neg, h1, h2, ← mul_add]
  have h3 := Complex.two_cos (x := ((t * x : ℝ) : ℂ))
  push_cast at h3 ⊢
  rw [← h3]

/-- Fourier representation as an integral of the triangle:
`k_T x = (1 / 2π) ∫_{-T}^{T} (1 - |t|/T) e^{-i t x} dt` (as a complex number). -/
theorem fejerKernel_eq_integral_exp {T : ℝ} (hT : 0 < T) (x : ℝ) :
    (fejerKernel T x : ℂ) =
      (1 / (2 * Real.pi) : ℝ) * ∫ t in (-T)..T,
        ((1 - |t| / T : ℝ) : ℂ) * Complex.exp (-((t * x : ℝ) * Complex.I)) := by
  set g : ℝ → ℂ := fun t => ((1 - |t| / T : ℝ) : ℂ) * Complex.exp (-((t * x : ℝ) * Complex.I))
    with hg
  have hgc : Continuous g := by
    rw [hg]
    fun_prop
  have hsplit : ∫ t in (-T)..T, g t = (∫ t in (-T)..0, g t) + ∫ t in (0 : ℝ)..T, g t :=
    (intervalIntegral.integral_add_adjacent_intervals (hgc.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _)).symm
  have hneg : ∫ t in (-T)..0, g t = ∫ t in (0 : ℝ)..T, g (-t) := by
    rw [intervalIntegral.integral_comp_neg]
    simp
  have hsum : (∫ t in (0 : ℝ)..T, g (-t)) + ∫ t in (0 : ℝ)..T, g t =
      ∫ t in (0 : ℝ)..T, (((1 - |t| / T) * (2 * Real.cos (t * x)) : ℝ) : ℂ) := by
    have hi : IntervalIntegrable (fun t => g (-t)) MeasureTheory.volume 0 T :=
      (hgc.comp continuous_neg).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add hi (hgc.intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr (fun t _ => fejer_exp_pair x t)
  have hreal : ∫ t in (0 : ℝ)..T, ((1 - |t| / T) * (2 * Real.cos (t * x))) =
      2 * ∫ t in (0 : ℝ)..T, (1 - t / T) * Real.cos (t * x) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le hT.le] at ht
    simp only [abs_of_nonneg ht.1]
    ring
  show ((fejerKernel T x : ℝ) : ℂ) = _
  rw [show ∫ t in (-T)..T, ((1 - |t| / T : ℝ) : ℂ) * Complex.exp (-((t * x : ℝ) * Complex.I)) =
    ∫ t in (-T)..T, g t from rfl, hsplit, hneg, hsum, intervalIntegral.integral_ofReal, hreal]
  rw [← Complex.ofReal_mul]
  congr 1
  unfold fejerKernel
  ring

/-- The triangle function `max 0 (1 - |x| / T)`, as a complex-valued function. -/
noncomputable def fejerTriangle (T x : ℝ) : ℂ := ((max 0 (1 - |x| / T) : ℝ) : ℂ)

/-- The triangle function is continuous. -/
lemma continuous_fejerTriangle (T : ℝ) : Continuous (fejerTriangle T) := by
  unfold fejerTriangle
  fun_prop

/-- The triangle function has compact support. -/
lemma hasCompactSupport_fejerTriangle {T : ℝ} (hT : 0 < T) :
    HasCompactSupport (fejerTriangle T) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -T) (b := T)) fun x hx => ?_
  have h : T < |x| := by
    by_contra hc
    exact hx (mem_Icc.2 (abs_le.1 (not_lt.1 hc)))
  have h1 : 1 - |x| / T ≤ 0 := by
    rw [sub_nonpos, one_le_div hT]
    exact h.le
  simp [fejerTriangle, max_eq_left h1]

/-- The integral of the triangle against a character is the interval integral. -/
lemma integral_fejerTriangle_exp {T : ℝ} (hT : 0 < T) (y : ℝ) :
    ∫ t : ℝ, Complex.exp (-((t * y : ℝ) * Complex.I)) * fejerTriangle T t =
      ∫ t in (-T)..T, ((1 - |t| / T : ℝ) : ℂ) * Complex.exp (-((t * y : ℝ) * Complex.I)) := by
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  have hzero : ∀ t : ℝ, t ∉ Ioc (-T) T →
      Complex.exp (-((t * y : ℝ) * Complex.I)) * fejerTriangle T t = 0 := by
    intro t ht
    have h : T ≤ |t| := by
      by_contra hc
      rw [not_le] at hc
      exact ht ⟨(abs_lt.1 hc).1, (abs_lt.1 hc).2.le⟩
    have h1 : 1 - |t| / T ≤ 0 := by
      rw [sub_nonpos, one_le_div hT]
      exact h
    simp [fejerTriangle, max_eq_left h1]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  have h : |t| ≤ T := abs_le.2 ⟨ht.1.le, ht.2⟩
  have h0 : 0 ≤ 1 - |t| / T := by
    rw [sub_nonneg, div_le_one hT]
    exact h
  simp only [fejerTriangle, max_eq_right h0]
  ring

/-- The Fourier transform of the triangle is `2π k_T (2π ξ)`. -/
lemma fourier_fejerTriangle {T : ℝ} (hT : 0 < T) (ξ : ℝ) :
    𝓕 (fejerTriangle T) ξ = ((2 * Real.pi * fejerKernel T (2 * Real.pi * ξ) : ℝ) : ℂ) := by
  rw [Real.fourier_eq']
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
  have h1 : ∀ v : ℝ, Complex.exp (↑(-2 * Real.pi * (ξ * v)) * Complex.I) =
      Complex.exp (-((v * (2 * Real.pi * ξ) : ℝ) * Complex.I)) := by
    intro v
    congr 1
    push_cast
    ring
  simp_rw [h1]
  rw [integral_fejerTriangle_exp hT, Complex.ofReal_mul,
    fejerKernel_eq_integral_exp hT (2 * Real.pi * ξ), ← mul_assoc, ← Complex.ofReal_mul]
  have h2 : 2 * Real.pi * (1 / (2 * Real.pi)) = 1 := by
    field_simp
  rw [h2]
  simp

/-- The Fejér kernel has total mass one. -/
theorem integral_fejerKernel {T : ℝ} (hT : 0 < T) : ∫ x, fejerKernel T x = 1 := by
  have hpi := Real.pi_pos
  have hωc := continuous_fejerTriangle T
  have hωi : Integrable (fejerTriangle T) :=
    hωc.integrable_of_hasCompactSupport (hasCompactSupport_fejerTriangle hT)
  have hF : 𝓕 (fejerTriangle T) =
      fun ξ => ((2 * Real.pi * fejerKernel T (2 * Real.pi * ξ) : ℝ) : ℂ) :=
    funext (fourier_fejerTriangle hT)
  have hFi : Integrable (𝓕 (fejerTriangle T)) := by
    rw [hF]
    exact (((integrable_fejerKernel hT).comp_mul_left' (R := 2 * Real.pi)
      (by positivity)).const_mul (2 * Real.pi)).ofReal
  have hinv := congrFun (hωc.fourierInv_fourier_eq hωi hFi) 0
  rw [Real.fourierInv_eq'] at hinv
  simp only [mul_zero, RCLike.inner_apply, conj_trivial, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_mul, smul_eq_mul] at hinv
  rw [hF] at hinv
  have h0 : fejerTriangle T 0 = 1 := by simp [fejerTriangle]
  beta_reduce at hinv
  rw [h0, integral_complex_ofReal] at hinv
  have hinv' : ∫ v : ℝ, 2 * Real.pi * fejerKernel T (2 * Real.pi * v) = 1 := by
    exact_mod_cast hinv
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x => fejerKernel T x) (2 * Real.pi),
    smul_eq_mul, abs_of_pos (inv_pos.2 (by positivity))] at hinv'
  field_simp at hinv'
  linarith

end LatticeProb
