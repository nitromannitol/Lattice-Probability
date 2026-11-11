import Mathlib

/-!
# Continuity of the circle average of a radial function

For `a : ℝ → ℝ` continuous on `(0,∞)` with `|a|^p` integrable on `(0,R]` for some `p > 2`, the circle
average `z ↦ Real.circleAverage (fun x ↦ a ‖x‖) z ε` is continuous on the closed ball `B_{R-ε}`.

Route (the near/far angular split):

* `radiusV ε t v = √((t-ε)² + 4tεv)` is the modulus of `t + ε e^{iθ}` when `v = (1 + cos θ)/2`. The
  circle average about `z` with `|z| = t` is `π⁻¹ ∫_0^1 a(radiusV ε t v) w(v) dv`, where
  `w(v) = (v(1-v))^{-1/2}` (`circleAverage_radial_eq`).
* The weight satisfies `w^q ∈ L¹(0,1)` for `q = p/(p-1) < 2`, which is where `p > 2` enters. The change
  of variables `v ↦ radiusV ε t v` gives `∫_0^1 g(radiusV ε t v) dv ≤ (2R/(4tε)) ∫_0^R g` (`integral_radiusV_le`),
  so for `t ≥ ε/2` the Hölder inequality bounds the `w`-integral of `g ∘ radiusV` by an `L^p(0,R)` norm.
* The truncations `max (-n) (min n a)` are bounded and continuous on `(0,∞)`, so their kernel integrals are
  continuous in `t` (dominated convergence). The remainder is bounded by the Hölder estimate applied to
  `(|a| - n)^+`, which tends to `0`; for `t ≤ ε/2` the radii lie in `[ε/2, R]`, where `a` is bounded, so the
  remainder vanishes for large `n`. The uniform limit is continuous.

Terminology: arcsine law / Chebyshev weight of the circle average; Hölder conjugate exponents.
-/

open Complex Filter Metric Real Set MeasureTheory Topology

noncomputable section

namespace LatticeProb.CircleAverageRadialContinuity

/-- The arcsine weight `w(v) = (v (1 - v))^{-1/2}` of the substitution `v = (1 + cos θ)/2`. -/
def arcW (v : ℝ) : ℝ := (v * (1 - v)) ^ (-(1 / 2 : ℝ))

/-- The radius `r(t,v) = √((t - ε)² + 4 t ε v)`; at `v = (1 + cos θ)/2` it is `|t + ε e^{iθ}|`. -/
def radiusV (ε t v : ℝ) : ℝ := √((t - ε) ^ 2 + 4 * t * ε * v)

/-- The radial kernel integral `∫_0^1 a(r(t,v)) w(v) dv`; the circle average of `a ∘ ‖·‖` about `z`
of radius `ε` is `π⁻¹` times this, at `t = ‖z‖` (`circleAverage_radial_eq`). -/
def radialKernelInt (a : ℝ → ℝ) (ε t : ℝ) : ℝ :=
  ∫ v in Ioo (0 : ℝ) 1, a (radiusV ε t v) * arcW v

/-! ### The arcsine weight -/

lemma arcW_nonneg {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) : 0 ≤ arcW v :=
  Real.rpow_nonneg (mul_nonneg hv.1.le (by linarith [hv.2])) _

lemma arcW_rpow_eq {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (q : ℝ) :
    arcW v ^ q = (v * (1 - v)) ^ (-(q / 2)) := by
  unfold arcW
  rw [← Real.rpow_mul (mul_nonneg hv.1.le (by linarith [hv.2]))]
  congr 1
  ring

lemma integrableOn_mul_one_sub_rpow_neg {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    IntegrableOn (fun v : ℝ => (v * (1 - v)) ^ (-s)) (Ioo (0 : ℝ) 1) := by
  have hI1 : IntegrableOn (fun v : ℝ => v ^ (-s)) (Ioo (0 : ℝ) 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2 (by linarith)
  have hI2 : IntegrableOn (fun v : ℝ => (1 - v) ^ (-s)) (Ioo (0 : ℝ) 1) := by
    have h := ((intervalIntegral.intervalIntegrable_rpow' (r := -s) (a := 0) (b := 1)
      (by linarith)).comp_sub_left 1)
    simp only [sub_zero, sub_self] at h
    have h2 := intervalIntegrable_iff.1 h
    rw [Set.uIoc_comm, Set.uIoc_of_le zero_le_one] at h2
    exact h2.mono_set Ioo_subset_Ioc_self
  refine Integrable.mono' ((hI1.add hI2).const_mul ((1 / 2 : ℝ) ^ (-s))) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    exact ContinuousOn.rpow_const (by fun_prop) fun v hv =>
      Or.inl (mul_pos hv.1 (by linarith [hv.2])).ne'
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    have hv0 : 0 < v := hv.1
    have hv1 : 0 < 1 - v := by linarith [hv.2]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (mul_nonneg hv0.le hv1.le) _),
      Real.mul_rpow hv0.le hv1.le]
    have hA : 0 ≤ v ^ (-s) := Real.rpow_nonneg hv0.le _
    have hB : 0 ≤ (1 - v) ^ (-s) := Real.rpow_nonneg hv1.le _
    rcases le_total v (1 / 2) with h | h
    · have hc : (1 - v) ^ (-s) ≤ (1 / 2 : ℝ) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by linarith)
      have hc0 : 0 ≤ (1 / 2 : ℝ) ^ (-s) := Real.rpow_nonneg (by norm_num) _
      have h1 := mul_le_mul_of_nonneg_left hc hA
      have h2 := mul_nonneg hc0 hB
      simp only [Pi.add_apply, mul_add]
      linarith [mul_comm (v ^ (-s)) ((1 / 2 : ℝ) ^ (-s))]
    · have hc : v ^ (-s) ≤ (1 / 2 : ℝ) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by linarith)
      have hc0 : 0 ≤ (1 / 2 : ℝ) ^ (-s) := Real.rpow_nonneg (by norm_num) _
      have h1 := mul_le_mul_of_nonneg_right hc hB
      have h2 := mul_nonneg hc0 hA
      simp only [Pi.add_apply, mul_add]
      linarith

/-- The arcsine weight has `w^q` integrable on `(0,1)` for `0 ≤ q < 2`: this is where `p > 2` enters
(`q = p/(p-1)` is the Hölder conjugate of `p`). -/
lemma integrableOn_arcW_rpow {q : ℝ} (hq0 : 0 ≤ q) (hq2 : q < 2) :
    IntegrableOn (fun v => arcW v ^ q) (Ioo (0 : ℝ) 1) := by
  have h := integrableOn_mul_one_sub_rpow_neg (s := q / 2) (by linarith) (by linarith)
  exact h.congr_fun (fun v hv => (arcW_rpow_eq hv q).symm) measurableSet_Ioo

/-! ### The radius `radiusV` and its change of variables -/

lemma radiusV_pos {ε t v : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) (hv : 0 < v) :
    0 < (t - ε) ^ 2 + 4 * t * ε * v := by
  rcases ht.eq_or_lt with h0 | ht'
  · subst h0
    nlinarith [mul_pos hε hε]
  · have : 0 < 4 * t * ε * v := by positivity
    nlinarith [sq_nonneg (t - ε)]

lemma hasDerivAt_radiusV {ε t v : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) (hv : 0 < v) :
    HasDerivAt (radiusV ε t) (4 * t * ε / (2 * radiusV ε t v)) v := by
  have h1 : HasDerivAt (fun y : ℝ => (t - ε) ^ 2 + 4 * t * ε * y) (4 * t * ε) v := by
    simpa using ((hasDerivAt_id v).const_mul (4 * t * ε)).const_add ((t - ε) ^ 2)
  exact h1.sqrt (radiusV_pos hε ht hv).ne'

lemma radiusV_injOn {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) : InjOn (radiusV ε t) (Ioo 0 1) := by
  intro v hv v' hv' h
  unfold radiusV at h
  have h2 := (Real.sqrt_inj (radiusV_pos hε ht.le hv.1).le
    (radiusV_pos hε ht.le hv'.1).le).1 h
  have hc : (4 * t * ε) ≠ 0 := by positivity
  exact mul_left_cancel₀ hc (by linarith : 4 * t * ε * v = 4 * t * ε * v')

lemma radiusV_mem_Ioc {ε t R v : ℝ} (hε : 0 < ε) (ht : 0 < t) (htR : t + ε ≤ R)
    (hv : v ∈ Ioo (0 : ℝ) 1) : radiusV ε t v ∈ Ioc 0 R := by
  refine ⟨Real.sqrt_pos.2 (radiusV_pos hε ht.le hv.1), ?_⟩
  unfold radiusV
  calc √((t - ε) ^ 2 + 4 * t * ε * v) ≤ √((t + ε) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [hv.2, mul_pos ht hε])
    _ = t + ε := Real.sqrt_sq (by linarith)
    _ ≤ R := htR

/-- **Change of variables** `v ↦ radiusV ε t v`: for `t > 0` and `t + ε ≤ R`, the `w`-free integral of
`g ∘ radiusV` over `(0,1)` is at most `(2R/(4tε)) ∫_0^R g`. -/
lemma integrableOn_and_integral_radiusV_le {g : ℝ → ℝ} {ε t R : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (htR : t + ε ≤ R) (hgc : ContinuousOn g (Ioi 0)) (hg0 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ g r)
    (hgi : IntegrableOn g (Ioc 0 R)) :
    IntegrableOn (fun v => g (radiusV ε t v)) (Ioo 0 1) ∧
      ∫ v in Ioo (0 : ℝ) 1, g (radiusV ε t v) ≤ (2 * R / (4 * t * ε)) * ∫ r in Ioc 0 R, g r := by
  have hD : 0 < 4 * t * ε := by positivity
  have hRpos : 0 ≤ 2 * R / (4 * t * ε) := div_nonneg (by linarith) hD.le
  have hderiv : ∀ v ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (radiusV ε t) (4 * t * ε / (2 * radiusV ε t v)) (Ioo 0 1) v :=
    fun v hv => (hasDerivAt_radiusV hε ht.le hv.1).hasDerivWithinAt
  have hinj := radiusV_injOn hε ht
  have hsub : radiusV ε t '' Ioo 0 1 ⊆ Ioc 0 R := by
    rintro _ ⟨v, hv, rfl⟩
    exact radiusV_mem_Ioc hε ht htR hv
  have hCOV := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj g
  have hIntImg : IntegrableOn g (radiusV ε t '' Ioo 0 1) := hgi.mono_set hsub
  have hIntRHS := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hderiv
    hinj g).1 hIntImg
  have hle : ∀ v ∈ Ioo (0 : ℝ) 1, g (radiusV ε t v) ≤
      2 * R / (4 * t * ε) * (|4 * t * ε / (2 * radiusV ε t v)| • g (radiusV ε t v)) := by
    intro v hv
    have hr := radiusV_mem_Ioc hε ht htR hv
    have hrpos : 0 < radiusV ε t v := hr.1
    have hrR : radiusV ε t v ≤ R := hr.2
    have hg : 0 ≤ g (radiusV ε t v) := hg0 _ hr.1
    rw [smul_eq_mul, abs_of_pos (div_pos hD (by linarith))]
    have key : 2 * R / (4 * t * ε) * (4 * t * ε / (2 * radiusV ε t v)) = R / radiusV ε t v := by
      field_simp
    have h1 : 1 ≤ R / radiusV ε t v := (one_le_div hrpos).2 hrR
    calc g (radiusV ε t v) ≤ R / radiusV ε t v * g (radiusV ε t v) :=
          le_mul_of_one_le_left hg h1
      _ = 2 * R / (4 * t * ε) * (4 * t * ε / (2 * radiusV ε t v)) * g (radiusV ε t v) := by
          rw [key]
      _ = _ := by ring
  have hcont : ContinuousOn (radiusV ε t) (Ioo 0 1) :=
    Continuous.continuousOn (by unfold radiusV; fun_prop)
  have hIntG : IntegrableOn (fun v => g (radiusV ε t v)) (Ioo 0 1) := by
    refine Integrable.mono' (hIntRHS.const_mul (2 * R / (4 * t * ε))) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
      exact hgc.comp hcont fun v hv => (radiusV_mem_Ioc hε ht htR hv).1
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      rw [Real.norm_of_nonneg (hg0 _ (radiusV_mem_Ioc hε ht htR hv).1)]
      exact hle v hv
  refine ⟨hIntG, ?_⟩
  calc ∫ v in Ioo (0 : ℝ) 1, g (radiusV ε t v)
      ≤ ∫ v in Ioo (0 : ℝ) 1, 2 * R / (4 * t * ε) *
          (|4 * t * ε / (2 * radiusV ε t v)| • g (radiusV ε t v)) := by
        refine integral_mono_of_nonneg ?_ (hIntRHS.const_mul (2 * R / (4 * t * ε))) ?_
        · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
          exact hg0 _ (radiusV_mem_Ioc hε ht htR hv).1
        · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
          exact hle v hv
    _ = 2 * R / (4 * t * ε) * ∫ v in Ioo (0 : ℝ) 1,
          |4 * t * ε / (2 * radiusV ε t v)| • g (radiusV ε t v) := integral_const_mul _ _
    _ = 2 * R / (4 * t * ε) * ∫ r in radiusV ε t '' Ioo 0 1, g r := by rw [hCOV]
    _ ≤ 2 * R / (4 * t * ε) * ∫ r in Ioc 0 R, g r := by
        refine mul_le_mul_of_nonneg_left ?_ hRpos
        refine setIntegral_mono_set hgi ?_ (Eventually.of_forall fun x hx => hsub hx)
        exact ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => hg0 r hr.1

/-! ### The circle average as a kernel integral -/

lemma norm_circle_radial_eq (t ε θ : ℝ) :
    ‖(t : ℂ) + (ε : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ =
      √(t ^ 2 + ε ^ 2 + 2 * t * ε * Real.cos θ) := by
  have h : ‖(t : ℂ) + (ε : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2 =
      t ^ 2 + ε ^ 2 + 2 * t * ε * Real.cos θ := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    linear_combination (ε ^ 2) * Real.sin_sq_add_cos_sq θ
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-- Rotation: `|z + ε e^{iθ}| = |t + ε e^{i(θ - arg z)}|` with `t = |z|`. -/
lemma norm_circle_eq_rotate (z : ℂ) (ε θ : ℝ) :
    ‖z + (ε : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ =
      ‖((‖z‖ : ℝ) : ℂ) + (ε : ℂ) * Complex.exp (((θ - Complex.arg z : ℝ) : ℂ) * Complex.I)‖ := by
  have hz : z = ((‖z‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg z : ℂ) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I z).symm
  have h2 : Complex.exp ((Complex.arg z : ℂ) * Complex.I) *
      Complex.exp (((θ - Complex.arg z : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have key : z + (ε : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) =
      Complex.exp ((Complex.arg z : ℂ) * Complex.I) *
        (((‖z‖ : ℝ) : ℂ) + (ε : ℂ) * Complex.exp (((θ - Complex.arg z : ℝ) : ℂ) * Complex.I)) := by
    linear_combination hz + (-(ε : ℂ)) * h2
  rw [key, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Periodic shift of the integral over one period. -/
lemma integral_rotate_two_pi (G : ℝ → ℝ) (hG : Function.Periodic G (2 * π)) (φ : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, G (θ - φ) = ∫ θ in (0 : ℝ)..2 * π, G θ := by
  rw [intervalIntegral.integral_comp_sub_right (f := G) (d := φ)]
  have h := hG.intervalIntegral_add_eq (-φ) 0
  rw [zero_add] at h
  rw [zero_sub, show 2 * π - φ = -φ + 2 * π by ring]
  exact h

/-- Reflection `θ ↦ 2π - θ` (no integrability needed for the reflected half). -/
lemma integral_two_pi_eq_two_mul_half (h : ℝ → ℝ) (hsymm : ∀ θ, h (2 * π - θ) = h θ)
    (hint : IntervalIntegrable h MeasureTheory.volume 0 π) :
    ∫ θ in (0 : ℝ)..2 * π, h θ = 2 * ∫ θ in (0 : ℝ)..π, h θ := by
  have hint2 : IntervalIntegrable h MeasureTheory.volume π (2 * π) := by
    have h' := hint.comp_sub_left (2 * π)
    simp only [hsymm] at h'
    rw [sub_zero, show 2 * π - π = π by ring] at h'
    rw [intervalIntegrable_iff] at h' ⊢
    rw [Set.uIoc_comm]
    exact h'
  rw [← intervalIntegral.integral_add_adjacent_intervals hint hint2]
  have hsecond : ∫ θ in π..2 * π, h θ = ∫ θ in (0 : ℝ)..π, h θ := by
    have h' := intervalIntegral.integral_comp_sub_left (f := h) (d := 2 * π) (a := 0) (b := π)
    simp only [hsymm] at h'
    rw [show 2 * π - π = π by ring, sub_zero] at h'
    exact h'.symm
  rw [hsecond]
  ring

lemma image_half_one_add_cos :
    (fun θ : ℝ => (1 + Real.cos θ) / 2) '' Ioo 0 π = Ioo 0 1 := by
  ext v
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    have h1 : Real.cos θ < 1 := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hθ.2.le hθ.1
      simpa using this
    have h2 : -1 < Real.cos θ := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1.le (le_refl π) hθ.2
      simpa using this
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hv0, hv1⟩
    refine ⟨Real.arccos (2 * v - 1), ⟨Real.arccos_pos.2 (by linarith),
      Real.arccos_lt_pi.2 (by linarith)⟩, ?_⟩
    simp only
    rw [Real.cos_arccos (by linarith) (by linarith)]
    ring

lemma injOn_half_one_add_cos : InjOn (fun θ : ℝ => (1 + Real.cos θ) / 2) (Ioo 0 π) := by
  intro x hx y hy hxy
  have hxy' : (1 + Real.cos x) / 2 = (1 + Real.cos y) / 2 := hxy
  have hc : Real.cos x = Real.cos y := by linarith
  exact Real.injOn_cos (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy) hc

lemma hasDerivAt_half_one_add_cos (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => (1 + Real.cos θ) / 2) (-Real.sin θ / 2) θ := by
  have := ((Real.hasDerivAt_cos θ).const_add 1).div_const 2
  simpa using this

/-- The pointwise identity behind the substitution `v = (1 + cos θ)/2` on `(0,π)`. -/
lemma integrand_half_eq {a : ℝ → ℝ} {ε t θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    |-Real.sin θ / 2| • (a (radiusV ε t ((1 + Real.cos θ) / 2)) * arcW ((1 + Real.cos θ) / 2)) =
      a (√(t ^ 2 + ε ^ 2 + 2 * t * ε * Real.cos θ)) := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hs' : Real.sin θ ≠ 0 := hs.ne'
  have habs : |-Real.sin θ / 2| = Real.sin θ / 2 := by
    rw [abs_div, abs_neg, abs_of_pos hs]
    norm_num
  have hv1 : (1 + Real.cos θ) / 2 * (1 - (1 + Real.cos θ) / 2) = (Real.sin θ / 2) ^ 2 := by
    linear_combination (-1 / 4 : ℝ) * Real.sin_sq_add_cos_sq θ
  have harc : arcW ((1 + Real.cos θ) / 2) = (Real.sin θ / 2)⁻¹ := by
    unfold arcW
    rw [hv1, ← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hs.le (by norm_num))]
    norm_num [Real.rpow_neg_one]
  have hr : radiusV ε t ((1 + Real.cos θ) / 2) = √(t ^ 2 + ε ^ 2 + 2 * t * ε * Real.cos θ) := by
    unfold radiusV
    congr 1
    ring
  rw [smul_eq_mul, habs, harc, hr]
  field_simp

/-- The arcsine kernel integral in the angle variable on `(0,π)`. -/
lemma integral_Ioo_pi_radial (a : ℝ → ℝ) (ε t : ℝ) :
    ∫ θ in Ioo 0 π, a (√(t ^ 2 + ε ^ 2 + 2 * t * ε * Real.cos θ)) = radialKernelInt a ε t := by
  have hCOV : ∫ v in Ioo (0 : ℝ) 1, a (radiusV ε t v) * arcW v =
      ∫ θ in Ioo 0 π, |-Real.sin θ / 2| •
        (a (radiusV ε t ((1 + Real.cos θ) / 2)) * arcW ((1 + Real.cos θ) / 2)) := by
    have h := integral_image_eq_integral_abs_deriv_smul (f' := fun θ => -Real.sin θ / 2)
      measurableSet_Ioo (fun θ _ => (hasDerivAt_half_one_add_cos θ).hasDerivWithinAt)
      injOn_half_one_add_cos (fun v => a (radiusV ε t v) * arcW v)
    rw [image_half_one_add_cos] at h
    exact h
  unfold radialKernelInt
  rw [hCOV]
  exact setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => (integrand_half_eq hθ).symm)

lemma integrableOn_Ioo_pi_radial_iff (a : ℝ → ℝ) (ε t : ℝ) :
    IntegrableOn (fun θ => a (√(t ^ 2 + ε ^ 2 + 2 * t * ε * Real.cos θ))) (Ioo 0 π) ↔
      IntegrableOn (fun v => a (radiusV ε t v) * arcW v) (Ioo 0 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (f' := fun θ => -Real.sin θ / 2)
    measurableSet_Ioo (fun θ _ => (hasDerivAt_half_one_add_cos θ).hasDerivWithinAt)
    injOn_half_one_add_cos (fun v => a (radiusV ε t v) * arcW v)
  rw [image_half_one_add_cos] at h
  exact (integrableOn_congr_fun (fun θ hθ => (integrand_half_eq hθ).symm)
    measurableSet_Ioo).trans h.symm

/-- **Circle average of a radial function.** For `|z| = t`, the circle average of `a ∘ ‖·‖` about `z`
of radius `ε` is `π⁻¹ ∫_0^1 a(r(t,v)) w(v) dv` (Chebyshev/arcsine substitution). -/
theorem circleAverage_radial_eq (a : ℝ → ℝ) {ε : ℝ} (z : ℂ)
    (hint : IntegrableOn (fun v => a (radiusV ε ‖z‖ v) * arcW v) (Ioo 0 1)) :
    Real.circleAverage (fun x : ℂ => a ‖x‖) z ε = π⁻¹ * radialKernelInt a ε ‖z‖ := by
  have hcirc : Real.circleAverage (fun x : ℂ => a ‖x‖) z ε =
      (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, a ‖z + (ε : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ := by
    rw [Real.circleAverage_def, smul_eq_mul]
    rfl
  have hper : Function.Periodic
      (fun s : ℝ => a ‖((‖z‖ : ℝ) : ℂ) + (ε : ℂ) * Complex.exp ((s : ℂ) * Complex.I)‖) (2 * π) := by
    intro s
    have e : Complex.exp (((s + 2 * π : ℝ) : ℂ) * Complex.I) = Complex.exp ((s : ℂ) * Complex.I) := by
      rw [show ((s + 2 * π : ℝ) : ℂ) * Complex.I = (s : ℂ) * Complex.I + 2 * π * Complex.I by
        push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    show a ‖((‖z‖ : ℝ) : ℂ) + (ε : ℂ) * Complex.exp (((s + 2 * π : ℝ) : ℂ) * Complex.I)‖ =
      a ‖((‖z‖ : ℝ) : ℂ) + (ε : ℂ) * Complex.exp ((s : ℂ) * Complex.I)‖
    rw [e]
  have hint_rot : ∫ θ in (0 : ℝ)..2 * π, a ‖z + (ε : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ =
      ∫ θ in (0 : ℝ)..2 * π, a (√(‖z‖ ^ 2 + ε ^ 2 + 2 * ‖z‖ * ε * Real.cos θ)) := by
    have e1 : ∫ θ in (0 : ℝ)..2 * π, a ‖z + (ε : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ =
        ∫ θ in (0 : ℝ)..2 * π, (fun s : ℝ => a ‖((‖z‖ : ℝ) : ℂ) +
          (ε : ℂ) * Complex.exp ((s : ℂ) * Complex.I)‖) (θ - Complex.arg z) :=
      intervalIntegral.integral_congr (fun θ _ => congrArg a (norm_circle_eq_rotate z ε θ))
    rw [e1, integral_rotate_two_pi _ hper]
    exact intervalIntegral.integral_congr (fun θ _ => by
      show a ‖((‖z‖ : ℝ) : ℂ) + (ε : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = _
      rw [norm_circle_radial_eq])
  have hint0π : IntervalIntegrable (fun θ => a (√(‖z‖ ^ 2 + ε ^ 2 + 2 * ‖z‖ * ε * Real.cos θ)))
      MeasureTheory.volume 0 π :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le Real.pi_pos.le).2
      ((integrableOn_Ioo_pi_radial_iff a ε ‖z‖).2 hint)
  have hsymm : ∀ θ, a (√(‖z‖ ^ 2 + ε ^ 2 + 2 * ‖z‖ * ε * Real.cos (2 * π - θ))) =
      a (√(‖z‖ ^ 2 + ε ^ 2 + 2 * ‖z‖ * ε * Real.cos θ)) := fun θ => by
    rw [Real.cos_two_pi_sub]
  rw [hcirc, hint_rot, integral_two_pi_eq_two_mul_half _ hsymm hint0π,
    intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo,
    integral_Ioo_pi_radial]
  ring

/-! ### Truncation and the Hölder estimate in the radial variable -/

lemma continuousOn_arcW : ContinuousOn arcW (Ioo (0 : ℝ) 1) := by
  unfold arcW
  refine ContinuousOn.rpow_const (by fun_prop) fun v hv => Or.inl ?_
  exact (mul_pos hv.1 (by linarith [hv.2])).ne'

lemma integrableOn_arcW : IntegrableOn arcW (Ioo (0 : ℝ) 1) := by
  simpa using integrableOn_arcW_rpow (q := 1) zero_le_one one_lt_two

lemma radiusV_le_add {ε t v : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) (hv : v ∈ Ioo (0 : ℝ) 1) :
    radiusV ε t v ≤ t + ε := by
  unfold radiusV
  calc √((t - ε) ^ 2 + 4 * t * ε * v) ≤ √((t + ε) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [mul_nonneg (mul_nonneg ht hε.le) (sub_nonneg.2 hv.2.le)])
    _ = t + ε := Real.sqrt_sq (by linarith)

/-- For `t ≤ ε/2` the radius stays above `ε/2`: the circle about `z` (`|z| = t`) avoids `B_{ε/2}(0)`. -/
lemma radiusV_ge_half {ε t v : ℝ} (hε : 0 < ε) (ht0 : 0 ≤ t) (ht : t ≤ ε / 2) (hv0 : 0 ≤ v) :
    ε / 2 ≤ radiusV ε t v := by
  unfold radiusV
  have h1 : ε / 2 ≤ ε - t := by linarith
  have h2 : (ε / 2) * (ε / 2) ≤ (ε - t) * (ε - t) := mul_le_mul h1 h1 (by linarith) (by linarith)
  calc ε / 2 = √((ε / 2) * (ε / 2)) := (Real.sqrt_mul_self (by linarith)).symm
    _ ≤ √((t - ε) ^ 2 + 4 * t * ε * v) :=
        Real.sqrt_le_sqrt (by nlinarith [mul_nonneg (mul_nonneg ht0 hε.le) hv0])

/-- The truncation `y ↦ max (-n) (min n y)` at level `n`. -/
def truncN (n y : ℝ) : ℝ := max (-n) (min n y)

lemma continuous_truncN (n : ℝ) : Continuous (truncN n) := by
  unfold truncN
  fun_prop

lemma truncN_eq_of_abs_le {n y : ℝ} (h : |y| ≤ n) : truncN n y = y := by
  have h1 : y ≤ n := by linarith [le_abs_self y]
  have h2 : -n ≤ y := by linarith [neg_abs_le y]
  unfold truncN
  rw [min_eq_right h1, max_eq_right h2]

/-- The truncation error is dominated by the excess `(|y| - n)^+`. -/
lemma sub_truncN_le {n : ℝ} (hn : 0 ≤ n) (y : ℝ) : |y - truncN n y| ≤ max (|y| - n) 0 := by
  unfold truncN
  rcases le_total y n with h1 | h1
  · rcases le_total (-n) y with h2 | h2
    · rw [min_eq_right h1, max_eq_right h2, sub_self, abs_zero]
      exact le_max_right _ _
    · rw [min_eq_right h1, max_eq_left h2]
      have h3 : y - -n ≤ 0 := by linarith
      rw [abs_of_nonpos h3]
      exact le_max_of_le_left (by linarith [neg_le_abs y])
  · rw [min_eq_left h1, max_eq_right (by linarith : -n ≤ n)]
    rw [abs_of_nonneg (by linarith : 0 ≤ y - n)]
    exact le_max_of_le_left (by linarith [le_abs_self y])

/-- The Hölder pair `p`, `q = p/(p-1)`: `1 < p`, `0 < q < 2` when `p > 2`. -/
lemma conjExponent_facts {p : ℝ} (hp : 2 < p) :
    1 < p ∧ 0 < Real.conjExponent p ∧ Real.conjExponent p < 2 ∧
      p.HolderConjugate (Real.conjExponent p) := by
  have hp1 : 1 < p := by linarith
  refine ⟨hp1, ?_, ?_, Real.HolderConjugate.conjExponent hp1⟩
  · unfold Real.conjExponent
    apply div_pos <;> linarith
  · unfold Real.conjExponent
    rw [div_lt_iff₀ (by linarith)]
    linarith

/-- The arcsine `L^q` norm of the weight, `q = p/(p-1)`. -/
def arcNorm (p : ℝ) : ℝ :=
  (∫ v in Ioo (0 : ℝ) 1, arcW v ^ Real.conjExponent p) ^ (1 / Real.conjExponent p)

/-- **Hölder estimate in the radial variable.** For `u ≥ 0` continuous on `(0,∞)` with `u^p` integrable on
`(0,R]` and `t ∈ [ε/2, R-ε]`: the weighted integral `∫_0^1 u(r(t,v)) w(v) dv` is integrable, and it is bounded
by `((R/ε²) ∫_0^R u^p)^{1/p} ‖w‖_{L^q}`. -/
lemma holder_radial {u : ℝ → ℝ} {p ε t R : ℝ} (hp : 2 < p) (hε : 0 < ε) (ht : ε / 2 ≤ t)
    (htR : t + ε ≤ R) (hu0 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ u r) (huc : ContinuousOn u (Ioi 0))
    (hui : IntegrableOn (fun r => u r ^ p) (Ioc 0 R)) :
    IntegrableOn (fun v => u (radiusV ε t v) * arcW v) (Ioo 0 1) ∧
      ∫ v in Ioo (0 : ℝ) 1, u (radiusV ε t v) * arcW v ≤
        ((R / ε ^ 2) * ∫ r in Ioc 0 R, u r ^ p) ^ (1 / p) * arcNorm p := by
  obtain ⟨hp1, hq0, hq2, hpq⟩ := conjExponent_facts hp
  have ht0 : 0 < t := by linarith
  have hR : 0 ≤ R := by linarith
  have hpos : ∀ v ∈ Ioo (0 : ℝ) 1, 0 < radiusV ε t v := fun v hv =>
    Real.sqrt_pos.2 (radiusV_pos hε ht0.le hv.1)
  have hgc : ContinuousOn (fun r => u r ^ p) (Ioi 0) :=
    huc.rpow_const (fun _ _ => Or.inr (by linarith))
  have hg0 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ u r ^ p := fun r hr => Real.rpow_nonneg (hu0 r hr) _
  obtain ⟨hIp, hleP⟩ := integrableOn_and_integral_radiusV_le hε ht0 htR hgc hg0 hui
  have hbdP : ∫ v in Ioo (0 : ℝ) 1, u (radiusV ε t v) ^ p ≤ (R / ε ^ 2) * ∫ r in Ioc 0 R, u r ^ p := by
    refine hleP.trans (mul_le_mul_of_nonneg_right ?_
      (setIntegral_nonneg measurableSet_Ioc (fun r hr => hg0 r hr.1)))
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hR hε.le) (by linarith : (0 : ℝ) ≤ 4 * t - 2 * ε)]
  have hur : ContinuousOn (fun v => u (radiusV ε t v)) (Ioo 0 1) :=
    huc.comp (Continuous.continuousOn (by unfold radiusV; fun_prop)) fun v hv => hpos v hv
  have hMemF : MemLp (fun v => u (radiusV ε t v)) (ENNReal.ofReal p)
      (MeasureTheory.volume.restrict (Ioo 0 1)) := by
    refine (integrable_norm_rpow_iff (hur.aestronglyMeasurable measurableSet_Ioo)
      (ENNReal.ofReal_pos.2 (by linarith)).ne' ENNReal.ofReal_ne_top).1 ?_
    rw [ENNReal.toReal_ofReal (by linarith)]
    refine hIp.congr_fun (fun v hv => ?_) measurableSet_Ioo
    simp only [Real.norm_of_nonneg (hu0 _ (hpos v hv))]
  have hMemW : MemLp arcW (ENNReal.ofReal (Real.conjExponent p))
      (MeasureTheory.volume.restrict (Ioo 0 1)) := by
    refine (integrable_norm_rpow_iff (continuousOn_arcW.aestronglyMeasurable measurableSet_Ioo)
      (ENNReal.ofReal_pos.2 hq0).ne' ENNReal.ofReal_ne_top).1 ?_
    rw [ENNReal.toReal_ofReal hq0.le]
    refine (integrableOn_arcW_rpow hq0.le hq2).congr_fun (fun v hv => ?_) measurableSet_Ioo
    simp only [Real.norm_of_nonneg (arcW_nonneg hv)]
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := MeasureTheory.volume.restrict (Ioo 0 1)) hpq
    ((ae_restrict_mem measurableSet_Ioo).mono fun v hv => hu0 _ (hpos v hv))
    ((ae_restrict_mem measurableSet_Ioo).mono fun v hv => arcW_nonneg hv) hMemF hMemW
  have hpow : (∫ v in Ioo (0 : ℝ) 1, u (radiusV ε t v) ^ p) ^ (1 / p) ≤
      ((R / ε ^ 2) * ∫ r in Ioc 0 R, u r ^ p) ^ (1 / p) :=
    Real.rpow_le_rpow (setIntegral_nonneg measurableSet_Ioo
      (fun v hv => Real.rpow_nonneg (hu0 _ (hpos v hv)) _)) hbdP
      (div_nonneg zero_le_one (by linarith))
  refine ⟨?_, hH.trans (mul_le_mul_of_nonneg_right hpow ?_)⟩
  · refine Integrable.mono' ((hIp.div_const p).add
      ((integrableOn_arcW_rpow hq0.le hq2).div_const (Real.conjExponent p)))
      ((hur.mul continuousOn_arcW).aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    rw [Real.norm_of_nonneg (mul_nonneg (hu0 _ (hpos v hv)) (arcW_nonneg hv))]
    exact Real.young_inequality_of_nonneg (hu0 _ (hpos v hv)) (arcW_nonneg hv) hpq
  · exact Real.rpow_nonneg (setIntegral_nonneg measurableSet_Ioo
      (fun v hv => Real.rpow_nonneg (arcW_nonneg hv) _)) _

lemma arcNorm_nonneg (p : ℝ) : 0 ≤ arcNorm p := by
  unfold arcNorm
  exact Real.rpow_nonneg (setIntegral_nonneg measurableSet_Ioo
    (fun v hv => Real.rpow_nonneg (arcW_nonneg hv) _)) _

lemma abs_truncN_le {n : ℝ} (hn : 0 ≤ n) (y : ℝ) : |truncN n y| ≤ n := by
  unfold truncN
  refine abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma continuousOn_a_radius {a : ℝ → ℝ} {ε t : ℝ} (ha : ContinuousOn a (Ioi 0)) (hε : 0 < ε)
    (ht0 : 0 ≤ t) : ContinuousOn (fun v => a (radiusV ε t v)) (Ioo 0 1) :=
  ha.comp (Continuous.continuousOn (by unfold radiusV; fun_prop)) fun v hv =>
    Real.sqrt_pos.2 (radiusV_pos hε ht0 hv.1)

lemma continuousOn_max_abs_sub {a : ℝ → ℝ} {n : ℝ} (ha : ContinuousOn a (Ioi 0)) :
    ContinuousOn (fun r => max (|a r| - n) 0) (Ioi 0) :=
  (continuous_id.max continuous_const : Continuous fun x : ℝ => max x 0).comp_continuousOn
    ((continuous_abs.comp_continuousOn ha).sub continuousOn_const)

/-- The continuous bound of `|a|` on the radial interval `[ε/2, R]`. -/
lemma exists_bound_Icc {a : ℝ → ℝ} {ε R : ℝ} (hε : 0 < ε) (ha : ContinuousOn a (Ioi 0)) :
    ∃ K0 : ℝ, ∀ x ∈ Icc (ε / 2) R, |a x| ≤ K0 := by
  obtain ⟨K0, hK⟩ := (isCompact_Icc (a := ε / 2) (b := R)).exists_bound_of_continuousOn
    (ha.mono fun x hx => lt_of_lt_of_le (half_pos hε) hx.1)
  exact ⟨K0, fun x hx => by simpa [Real.norm_eq_abs] using hK x hx⟩

/-- The radial integrand is integrable on `(0,1)` for `t ∈ [0, R-ε]`. -/
lemma integrableOn_radial_of_mem {a : ℝ → ℝ} {p ε R : ℝ} (hp : 2 < p) (hε : 0 < ε)
    (ha : ContinuousOn a (Ioi 0)) (hLp : IntegrableOn (fun r => |a r| ^ p) (Ioc 0 R)) {t : ℝ}
    (ht : t ∈ Icc 0 (R - ε)) :
    IntegrableOn (fun v => a (radiusV ε t v) * arcW v) (Ioo 0 1) := by
  obtain ⟨ht0, htT⟩ := ht
  have htR : t + ε ≤ R := by linarith
  rcases le_total t (ε / 2) with h | h
  · obtain ⟨K0, hK0⟩ := exists_bound_Icc hε ha
    refine Integrable.mono' (integrableOn_arcW.const_mul K0)
      ((continuousOn_a_radius ha hε ht0).mul continuousOn_arcW |>.aestronglyMeasurable
        measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    have hrad : ε / 2 ≤ radiusV ε t v := radiusV_ge_half hε ht0 h hv.1.le
    have hrR : radiusV ε t v ≤ R := le_trans (radiusV_le_add hε ht0 hv) htR
    have hK := hK0 _ ⟨hrad, hrR⟩
    rw [norm_mul, Real.norm_of_nonneg (arcW_nonneg hv), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hK (arcW_nonneg hv)
  · have hI := (holder_radial (u := fun r => |a r|) hp hε h htR (fun r _ => abs_nonneg _)
      (continuous_abs.comp_continuousOn ha) hLp).1
    refine Integrable.mono' hI
      ((continuousOn_a_radius ha hε ht0).mul continuousOn_arcW |>.aestronglyMeasurable
        measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    rw [norm_mul, Real.norm_of_nonneg (arcW_nonneg hv), Real.norm_eq_abs]

/-- The truncated kernel integral is continuous in `t` (dominated convergence). -/
lemma continuousOn_truncKernel {a : ℝ → ℝ} {ε R : ℝ} (hε : 0 < ε) (ha : ContinuousOn a (Ioi 0))
    {n : ℝ} (hn : 0 ≤ n) :
    ContinuousOn (fun t => ∫ v in Ioo (0 : ℝ) 1, truncN n (a (radiusV ε t v)) * arcW v)
      (Icc 0 (R - ε)) := by
  intro t0 ht0
  unfold ContinuousWithinAt
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun v => n * arcW v) ?_ ?_
    (integrableOn_arcW.const_mul n) ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ((continuous_truncN n).comp_continuousOn (continuousOn_a_radius ha hε ht.1)
      |>.mul continuousOn_arcW).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    rw [norm_mul, Real.norm_of_nonneg (arcW_nonneg hv)]
    exact mul_le_mul_of_nonneg_right (abs_truncN_le hn _) (arcW_nonneg hv)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    have hpos0 : 0 < radiusV ε t0 v := Real.sqrt_pos.2 (radiusV_pos hε ht0.1 hv.1)
    have hc : ContinuousAt (fun t => radiusV ε t v) t0 :=
      Continuous.continuousAt (by unfold radiusV; fun_prop)
    have ha' : ContinuousAt a (radiusV ε t0 v) := ha.continuousAt (Ioi_mem_nhds hpos0)
    have hA : ContinuousAt (fun t => a (radiusV ε t v)) t0 :=
      (ha.continuousAt (Ioi_mem_nhds hpos0)).tendsto.comp hc.tendsto
    have hT : ContinuousAt (fun t => truncN n (a (radiusV ε t v))) t0 :=
      (continuous_truncN n).continuousAt.comp hA
    exact (hT.mul_const (arcW v)).tendsto.mono_left nhdsWithin_le_nhds

/-- `κ_n(a) = ∫_0^R (|a| - n)_+^p`, the `L^p` excess of `a` above the level `n`. -/
def kappaN (a : ℝ → ℝ) (R p n : ℝ) : ℝ := ∫ r in Ioc 0 R, (max (|a r| - n) 0) ^ p

/-- The uniform error bound `δ_n = ((R/ε²) κ_n)^{1/p} ‖w‖_{L^q}`. -/
def deltaN (a : ℝ → ℝ) (ε R p n : ℝ) : ℝ := ((R / ε ^ 2) * kappaN a R p n) ^ (1 / p) * arcNorm p

lemma kappaN_nonneg (a : ℝ → ℝ) (R p n : ℝ) : 0 ≤ kappaN a R p n :=
  setIntegral_nonneg measurableSet_Ioc (fun _ _ => Real.rpow_nonneg (le_max_right _ _) _)

lemma deltaN_nonneg {a : ℝ → ℝ} {ε R p : ℝ} (hR : 0 ≤ R) (n : ℝ) : 0 ≤ deltaN a ε R p n :=
  mul_nonneg (Real.rpow_nonneg (mul_nonneg (div_nonneg hR (sq_nonneg _)) (kappaN_nonneg a R p n)) _)
    (arcNorm_nonneg p)

/-- `κ_n → 0` as `n → ∞` (dominated convergence, the integrand is dominated by `|a|^p`). -/
lemma tendsto_kappaN {a : ℝ → ℝ} {p R : ℝ} (hp : 2 < p) (ha : ContinuousOn a (Ioi 0))
    (hLp : IntegrableOn (fun r => |a r| ^ p) (Ioc 0 R)) :
    Tendsto (fun n : ℕ => kappaN a R p n) atTop (𝓝 0) := by
  unfold kappaN
  have hF : ∀ᶠ n : ℕ in atTop,
      AEStronglyMeasurable (fun r => (max (|a r| - (n : ℝ)) 0) ^ p) (volume.restrict (Ioc 0 R)) :=
    Eventually.of_forall fun n => by
      have hc : ContinuousOn (fun r => (max (|a r| - (n : ℝ)) 0) ^ p) (Ioi 0) :=
        (continuousOn_max_abs_sub (n := (n : ℝ)) ha).rpow_const
          (fun _ _ => Or.inr (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
      exact (hc.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
  have hbd : ∀ᶠ n : ℕ in atTop, ∀ᵐ r ∂(volume.restrict (Ioc 0 R)),
      ‖(max (|a r| - (n : ℝ)) 0) ^ p‖ ≤ |a r| ^ p :=
    Eventually.of_forall fun n => by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_max_right _ _) _)]
      exact Real.rpow_le_rpow (le_max_right _ _)
        (max_le (by linarith [abs_nonneg (a r)]) (abs_nonneg _)) (by linarith)
  have hlim : ∀ᵐ r ∂(volume.restrict (Ioc 0 R)),
      Tendsto (fun n : ℕ => (max (|a r| - (n : ℝ)) 0) ^ p) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (|a r|)] with n hn
    rw [max_eq_right (show |a r| - (n : ℝ) ≤ 0 by linarith),
      Real.zero_rpow (show p ≠ 0 from (by linarith : (0 : ℝ) < p).ne')]
  have := MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun r => |a r| ^ p)
    hF hbd hLp hlim
  simpa using this

/-- The uniform bound `δ_n → 0`. -/
lemma tendsto_deltaN {a : ℝ → ℝ} {ε R p : ℝ} (hp : 2 < p) (ha : ContinuousOn a (Ioi 0))
    (hLp : IntegrableOn (fun r => |a r| ^ p) (Ioc 0 R)) :
    Tendsto (fun n : ℕ => deltaN a ε R p n) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (R / ε ^ 2) * kappaN a R p n) atTop (𝓝 0) := by
    simpa using (tendsto_kappaN hp ha hLp).const_mul (R / ε ^ 2)
  -- (ε > 0 is not needed for the limit)
  have hpos : (0 : ℝ) < 1 / p := one_div_pos.2 (by linarith)
  have h2 : Tendsto (fun n : ℕ => ((R / ε ^ 2) * kappaN a R p n) ^ (1 / p)) atTop (𝓝 0) := by
    have hc : Continuous (fun x : ℝ => x ^ (1 / p)) := Real.continuous_rpow_const hpos.le
    have := (hc.tendsto 0).comp h1
    rwa [Real.zero_rpow hpos.ne'] at this
  unfold deltaN
  simpa using h2.mul_const (arcNorm p)

/-- **Continuity of the radial kernel integral** `t ↦ ∫_0^1 a(r(t,v)) w(v) dv` on `[0, R-ε]`:
uniform limit of the truncated kernels, which are continuous by dominated convergence. -/
lemma continuousOn_radialKernelInt {a : ℝ → ℝ} {ε R p : ℝ} (hp : 2 < p) (hε : 0 < ε)
    (ha : ContinuousOn a (Ioi 0)) (hLp : IntegrableOn (fun r => |a r| ^ p) (Ioc 0 R)) :
    ContinuousOn (fun t => radialKernelInt a ε t) (Icc 0 (R - ε)) := by
  obtain ⟨K0, hK0⟩ := exists_bound_Icc hε ha
  have hE1 : ∀ n : ℕ, K0 ≤ (n : ℝ) → ∀ t ∈ Icc 0 (R - ε),
      ‖radialKernelInt a ε t - ∫ v in Ioo (0 : ℝ) 1, truncN n (a (radiusV ε t v)) * arcW v‖ ≤
        deltaN a ε R p n := by
    intro n hn t ht
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hR : 0 ≤ R := by linarith [ht.1, ht.2]
    rcases le_total t (ε / 2) with h | h
    · have hEq : ∫ v in Ioo (0 : ℝ) 1, truncN n (a (radiusV ε t v)) * arcW v =
          radialKernelInt a ε t := by
        unfold radialKernelInt
        refine setIntegral_congr_fun measurableSet_Ioo (fun v hv => ?_)
        have hrad : ε / 2 ≤ radiusV ε t v := radiusV_ge_half hε ht.1 h hv.1.le
        have hrR : radiusV ε t v ≤ R := le_trans (radiusV_le_add hε ht.1 hv) (by linarith [ht.2])
        rw [truncN_eq_of_abs_le ((hK0 _ ⟨hrad, hrR⟩).trans hn)]
      rw [hEq, sub_self, norm_zero]
      exact deltaN_nonneg hR _
    · have hu0 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ max (|a r| - (n : ℝ)) 0 := fun r _ => le_max_right _ _
      have hcu : ContinuousOn (fun r => max (|a r| - (n : ℝ)) 0) (Ioi 0) :=
        continuousOn_max_abs_sub (n := (n : ℝ)) ha
      have hui : IntegrableOn (fun r => (max (|a r| - (n : ℝ)) 0) ^ p) (Ioc 0 R) := by
        refine Integrable.mono' hLp ?_ ?_
        · exact ((hcu.rpow_const (fun _ _ => Or.inr (by linarith))).mono Ioc_subset_Ioi_self)
            |>.aestronglyMeasurable measurableSet_Ioc
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
          rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_max_right _ _) _)]
          exact Real.rpow_le_rpow (le_max_right _ _)
            (max_le (by linarith [abs_nonneg (a r)]) (abs_nonneg _)) (by linarith)
      have hA := holder_radial (u := fun r => max (|a r| - (n : ℝ)) 0) hp hε h
        (by linarith [ht.2]) hu0 hcu hui
      have hI_abs : IntegrableOn (fun v => |a (radiusV ε t v)| * arcW v) (Ioo 0 1) :=
        (holder_radial (u := fun r => |a r|) hp hε h (by linarith [ht.2])
          (fun r _ => abs_nonneg _) (continuous_abs.comp_continuousOn ha) hLp).1
      have hI_a : IntegrableOn (fun v => a (radiusV ε t v) * arcW v) (Ioo 0 1) :=
        integrableOn_radial_of_mem hp hε ha hLp ht
      have hI_T : IntegrableOn (fun v => truncN n (a (radiusV ε t v)) * arcW v) (Ioo 0 1) := by
        refine Integrable.mono' (integrableOn_arcW.const_mul n)
          (((continuous_truncN n).comp_continuousOn (continuousOn_a_radius ha hε ht.1)).mul
            continuousOn_arcW |>.aestronglyMeasurable measurableSet_Ioo) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
        rw [norm_mul, Real.norm_of_nonneg (arcW_nonneg hv)]
        exact mul_le_mul_of_nonneg_right (abs_truncN_le hn0 _) (arcW_nonneg hv)
      have key : radialKernelInt a ε t - ∫ v in Ioo (0 : ℝ) 1, truncN n (a (radiusV ε t v)) * arcW v =
          ∫ v in Ioo (0 : ℝ) 1, (a (radiusV ε t v) - truncN n (a (radiusV ε t v))) * arcW v := by
        unfold radialKernelInt
        rw [← integral_sub hI_a hI_T]
        simp only [sub_mul]
      rw [key]
      refine (norm_integral_le_integral_norm _).trans ?_
      refine (integral_mono_of_nonneg (ae_of_all _ fun v => norm_nonneg _) hA.1 ?_).trans hA.2
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      rw [norm_mul, Real.norm_of_nonneg (arcW_nonneg hv), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (sub_truncN_le hn0 _) (arcW_nonneg hv)
  have hunif : TendstoUniformlyOn
      (fun (n : ℕ) (t : ℝ) => ∫ v in Ioo (0 : ℝ) 1, truncN n (a (radiusV ε t v)) * arcW v)
      (fun t => radialKernelInt a ε t) atTop (Icc 0 (R - ε)) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro e he
    filter_upwards [(tendsto_order.1 (tendsto_deltaN hp ha hLp)).2 e he,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop K0] with n hδ hK t ht
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hE1 n hK t ht) hδ
  exact hunif.continuousOn (Eventually.of_forall fun n =>
    continuousOn_truncKernel (R := R) hε ha (Nat.cast_nonneg n)).frequently

/-- **Continuity of the circle average of a radial function**. For `a` continuous on
`(0,∞)` with `|a|^p` integrable on `(0,R]`, `p > 2`, the circle average
`z ↦ Real.circleAverage (fun x ↦ a ‖x‖) z ε` is continuous on the closed ball of radius `R - ε`. -/
theorem continuous_circleAverage_radial_of_memLp
    {a : ℝ → ℝ} {ε R p : ℝ}
    (hε : 0 < ε)
    (hp : 2 < p)
    (ha : ContinuousOn a (Set.Ioi 0))
    (haLp :
      IntegrableOn
        (fun r => |a r| ^ p)
        (Set.Ioc 0 R)) :
    ContinuousOn
      (fun z =>
        Real.circleAverage
          (fun x : ℂ => a ‖x‖) z ε)
      (Metric.closedBall (0 : ℂ) (R - ε)) := by
  have hΦ := continuousOn_radialKernelInt hp hε ha haLp
  have hcomp : ContinuousOn (fun z : ℂ => π⁻¹ * radialKernelInt a ε ‖z‖)
      (Metric.closedBall (0 : ℂ) (R - ε)) :=
    continuousOn_const.mul (hΦ.comp continuous_norm.continuousOn fun z hz =>
      ⟨norm_nonneg _, by simpa using hz⟩)
  refine hcomp.congr fun z hz => ?_
  exact circleAverage_radial_eq a z (integrableOn_radial_of_mem hp hε ha haLp
    ⟨norm_nonneg _, by simpa using hz⟩)

end LatticeProb.CircleAverageRadialContinuity
