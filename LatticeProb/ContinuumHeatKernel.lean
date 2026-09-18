/-
The one-dimensional Brownian heat kernel with variance `t/4`. Its square integral
and the square integrability of its time-truncated test functions define the
space-time white-noise pairing.
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory ProbabilityTheory

noncomputable section

namespace LatticeProb.ContinuumStopping

/-- **The square of the Gaussian density is the density of half the variance,
times `(2√(πv))⁻¹`.** -/
theorem gaussianPDFReal_sq (m : ℝ) {v : NNReal} (hv : v ≠ 0) (y : ℝ) :
    (gaussianPDFReal m v y) ^ 2
      = (2 * Real.sqrt (Real.pi * v))⁻¹ * gaussianPDFReal m (v / 2) y := by
  have hvpos : (0 : ℝ) < (v : ℝ) := by
    rcases v.coe_nonneg.lt_or_eq with h | h
    · exact h
    · exact absurd (by exact_mod_cast h.symm : v = 0) hv
  have hc : ((v / 2 : NNReal) : ℝ) = (v : ℝ) / 2 := by push_cast; ring
  have hs2 : Real.sqrt (2 * Real.pi * ((v : ℝ) / 2)) = Real.sqrt (Real.pi * (v : ℝ)) := by
    congr 1
    ring
  have hexp : Real.exp (-(y - m) ^ 2 / (2 * (v : ℝ))) ^ 2
      = Real.exp (-(y - m) ^ 2 / (2 * ((v : ℝ) / 2))) := by
    rw [sq, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hsq1 : Real.sqrt (2 * Real.pi * (v : ℝ)) ^ 2 = 2 * Real.pi * (v : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsq2 : Real.sqrt (Real.pi * (v : ℝ)) ^ 2 = Real.pi * (v : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hprod : Real.sqrt (Real.pi * (v : ℝ)) * Real.sqrt (Real.pi * (v : ℝ))
      = Real.pi * (v : ℝ) := by
    rw [← sq]
    exact hsq2
  have hconst : ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) ^ 2
      = (2 * Real.sqrt (Real.pi * (v : ℝ)))⁻¹ * (Real.sqrt (Real.pi * (v : ℝ)))⁻¹ := by
    rw [inv_pow, hsq1, ← mul_inv]
    congr 1
    calc 2 * Real.pi * (v : ℝ) = 2 * (Real.pi * (v : ℝ)) := by ring
      _ = 2 * (Real.sqrt (Real.pi * (v : ℝ)) * Real.sqrt (Real.pi * (v : ℝ))) := by rw [hprod]
      _ = 2 * Real.sqrt (Real.pi * (v : ℝ)) * Real.sqrt (Real.pi * (v : ℝ)) := by ring
  simp only [gaussianPDFReal, hc, mul_pow, hexp, hs2, hconst]
  ring

theorem half_ne_zero_of_ne_zero {v : NNReal} (hv : v ≠ 0) : (v / 2 : NNReal) ≠ 0 := by
  intro h
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · exact hv h
  · norm_num at h

/-- The square of the Gaussian density is integrable. -/
theorem integrable_gaussianPDFReal_sq (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    Integrable (fun y : ℝ => (gaussianPDFReal m v y) ^ 2) := by
  have hpt : (fun y : ℝ => (gaussianPDFReal m v y) ^ 2)
      = fun y : ℝ => (2 * Real.sqrt (Real.pi * v))⁻¹ * gaussianPDFReal m (v / 2) y :=
    funext fun y => gaussianPDFReal_sq m hv y
  rw [hpt]
  exact (integrable_gaussianPDFReal m (v / 2)).const_mul _

/-- The square of the Gaussian density integrates to `(2√(πv))⁻¹`. -/
theorem integral_gaussianPDFReal_sq (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    ∫ y : ℝ, (gaussianPDFReal m v y) ^ 2 = (2 * Real.sqrt (Real.pi * v))⁻¹ := by
  have hpt : (fun y : ℝ => (gaussianPDFReal m v y) ^ 2)
      = fun y : ℝ => (2 * Real.sqrt (Real.pi * v))⁻¹ * gaussianPDFReal m (v / 2) y :=
    funext fun y => gaussianPDFReal_sq m hv y
  rw [hpt, integral_const_mul,
    integral_gaussianPDFReal_eq_one m (half_ne_zero_of_ne_zero hv), mul_one]

/-- The transition density of the Brownian motion with `Var(B_t) = t/4`, with
generator `Δ/8`. -/
def contHeat (t x y : ℝ) : ℝ := gaussianPDFReal x (Real.toNNReal (t / 4)) y

theorem toNNReal_ne_zero_of_pos {t : ℝ} (ht : 0 < t) : Real.toNNReal (t / 4) ≠ 0 := by
  intro h
  rw [Real.toNNReal_eq_zero] at h
  linarith

/-- The square of the transition density integrates to `(√(πt))⁻¹`, so it is
integrable in the time variable near zero. -/
theorem integral_contHeat_sq {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∫ y : ℝ, (contHeat t x y) ^ 2 = (Real.sqrt (Real.pi * t))⁻¹ := by
  have hne : Real.toNNReal (t / 4) ≠ 0 := toNNReal_ne_zero_of_pos ht
  have hcoe : ((Real.toNNReal (t / 4) : NNReal) : ℝ) = t / 4 :=
    Real.coe_toNNReal _ (by positivity)
  have hsq : Real.sqrt (Real.pi * (t / 4)) = Real.sqrt (Real.pi * t) / 2 := by
    have h1 : Real.pi * (t / 4) = (Real.sqrt (Real.pi * t) / 2) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by positivity)]
      ring
    rw [h1, Real.sqrt_sq (by positivity)]
  unfold contHeat
  rw [integral_gaussianPDFReal_sq x hne, hcoe, hsq,
    show (2 : ℝ) * (Real.sqrt (Real.pi * t) / 2) = Real.sqrt (Real.pi * t) by ring]

theorem contHeat_nonneg (t x y : ℝ) : 0 ≤ contHeat t x y := gaussianPDFReal_nonneg _ _ _

/-- The square of the transition density is integrable in space. -/
theorem integrable_contHeat_sq {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (fun y : ℝ => (contHeat t x y) ^ 2) :=
  integrable_gaussianPDFReal_sq x (toNNReal_ne_zero_of_pos ht)

/-- The test function of the space-time noise field: the heat kernel of the
elapsed time, truncated to the time window `(s, T)`.  Pairing the white noise
with it is `Z_T(s, x)` up to the intensity factor `sqrt(v)`. -/
def contNoiseTest (T s x : ℝ) : ℝ × ℝ → ℝ :=
  fun p => if s < p.1 ∧ p.1 < T then contHeat (p.1 - s) x p.2 else 0

theorem measurable_contHeat_uncurry (x : ℝ) :
    Measurable fun p : ℝ × ℝ => contHeat p.1 x p.2 := by
  have h : (fun p : ℝ × ℝ => contHeat p.1 x p.2)
      = (fun q : ℝ × NNReal × ℝ => gaussianPDFReal q.1 q.2.1 q.2.2) ∘
        (fun p : ℝ × ℝ => (x, (Real.toNNReal (p.1 / 4), p.2))) := rfl
  rw [h]
  refine measurable_uncurry_gaussianPDFReal.comp (measurable_const.prodMk ?_)
  exact ((measurable_fst.div_const 4).real_toNNReal.prodMk measurable_snd)

theorem measurable_contNoiseTest (T s x : ℝ) : Measurable (contNoiseTest T s x) := by
  classical
  have hset : MeasurableSet {p : ℝ × ℝ | s < p.1 ∧ p.1 < T} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_const)
  refine Measurable.ite hset ?_ measurable_const
  exact (measurable_contHeat_uncurry x).comp ((measurable_fst.sub_const s).prodMk measurable_snd)

/-- The inverse square root singularity of the time integral is integrable:
`∫_s^T (π(t-s))^{-1/2} dt < ∞`.  This is what makes the space-time noise field
well defined in one space dimension. -/
theorem integrableOn_inv_sqrt_pi_sub (s T : ℝ) :
    IntegrableOn (fun t : ℝ => (Real.sqrt (Real.pi * (t - s)))⁻¹) (Set.Ioo s T) volume := by
  by_cases hTs : T ≤ s
  · rw [Set.Ioo_eq_empty (not_lt.mpr hTs)]
    simp
  · replace hTs : s < T := lt_of_not_ge hTs
    have hbase : IntervalIntegrable (fun x : ℝ => x ^ (-(1/2) : ℝ)) volume 0 (T - s) :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have hshift : IntervalIntegrable (fun t : ℝ => (t - s) ^ (-(1/2) : ℝ)) volume
        (0 + s) (T - s + s) := hbase.comp_sub_right s
    rw [zero_add, sub_add_cancel] at hshift
    have h1 : IntegrableOn (fun t : ℝ => (t - s) ^ (-(1/2) : ℝ)) (Set.Ioo s T) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hTs.le).mp hshift
    have h2 : IntegrableOn (fun t : ℝ => (Real.sqrt Real.pi)⁻¹ * (t - s) ^ (-(1/2) : ℝ))
        (Set.Ioo s T) volume := h1.const_mul _
    refine h2.congr_fun ?_ measurableSet_Ioo
    intro t ht
    have hts : (0 : ℝ) < t - s := sub_pos.mpr ht.1
    show (Real.sqrt Real.pi)⁻¹ * (t - s) ^ (-(1/2) : ℝ) = (Real.sqrt (Real.pi * (t - s)))⁻¹
    rw [Real.sqrt_mul Real.pi_pos.le, mul_inv, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      Real.rpow_neg hts.le]

/-- **The square of the test function is integrable on the plane.**  By Tonelli:
its space integral at time `t` is `(π(t-s))^{-1/2}` on the window `(s,T)` and
zero outside, and that is integrable in `t`. -/
theorem integrable_contNoiseTest_sq (T s x : ℝ) :
    Integrable (fun p : ℝ × ℝ => (contNoiseTest T s x p) ^ 2)
      (volume : Measure (ℝ × ℝ)) := by
  have h1 : IntegrableOn (fun t : ℝ => (Real.sqrt (Real.pi * (t - s)))⁻¹)
      (Set.Ioo s T) volume := integrableOn_inv_sqrt_pi_sub s T
  have hmeas : Measurable (fun p : ℝ × ℝ => (contNoiseTest T s x p) ^ 2) :=
    (measurable_contNoiseTest T s x).pow_const 2
  rw [MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall (fun t => ?_), ?_⟩
  · by_cases hc : s < t ∧ t < T
    · have ht : (0 : ℝ) < t - s := sub_pos.mpr hc.1
      simpa [contNoiseTest, hc] using integrable_contHeat_sq ht x
    · simp [contNoiseTest, hc]
  · have hfun : (fun t : ℝ => ∫ y : ℝ, ‖(contNoiseTest T s x (t, y)) ^ 2‖)
        = Set.indicator (Set.Ioo s T) (fun t : ℝ => (Real.sqrt (Real.pi * (t - s)))⁻¹) := by
      funext t
      by_cases hc : s < t ∧ t < T
      · have ht : (0 : ℝ) < t - s := sub_pos.mpr hc.1
        have hval : (∫ y : ℝ, ‖(contNoiseTest T s x (t, y)) ^ 2‖)
            = ∫ y : ℝ, (contHeat (t - s) x y) ^ 2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
          show ‖contNoiseTest T s x (t, y) ^ 2‖ = contHeat (t - s) x y ^ 2
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          simp [contNoiseTest, hc]
        rw [hval, integral_contHeat_sq ht x, Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨hc.1, hc.2⟩)]
      · simp [contNoiseTest, hc, Set.mem_Ioo]
    rw [hfun]
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).mpr h1

/-- **The test function of the space-time noise field is square integrable on
the plane**, so `Z_T(s,x)` is a legitimate white-noise integral. -/
theorem memLp_contNoiseTest (T s x : ℝ) :
    MemLp (contNoiseTest T s x) 2 (volume : Measure (ℝ × ℝ)) :=
  (memLp_two_iff_integrable_sq
    (measurable_contNoiseTest T s x).aestronglyMeasurable).mpr
    (integrable_contNoiseTest_sq T s x)

/-- The time integral of the singularity: `∫_s^T (π(t-s))^{-1/2} dt = 2√(T-s)/√π`. -/
theorem integral_inv_sqrt_pi_sub {s T : ℝ} (hsT : s ≤ T) :
    (∫ t in Set.Ioo s T, (Real.sqrt (Real.pi * (t - s)))⁻¹)
      = 2 * Real.sqrt (T - s) / Real.sqrt Real.pi := by
  have hcongr : (∫ t in Set.Ioo s T, (Real.sqrt (Real.pi * (t - s)))⁻¹)
      = ∫ t in Set.Ioo s T, (Real.sqrt Real.pi)⁻¹ * (t - s) ^ (-(1/2) : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    have hts : (0 : ℝ) < t - s := sub_pos.mpr ht.1
    rw [Real.sqrt_mul Real.pi_pos.le, mul_inv, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      Real.rpow_neg hts.le]
  rw [hcongr, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hsT, intervalIntegral.integral_const_mul]
  have hsub : (∫ t in s..T, (t - s) ^ (-(1/2) : ℝ)) = ∫ t in (s - s)..(T - s), t ^ (-(1/2) : ℝ) :=
    intervalIntegral.integral_comp_sub_right (fun t : ℝ => t ^ (-(1/2) : ℝ)) s
  rw [hsub, sub_self, integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1/2)))]
  rw [Real.zero_rpow (by norm_num)]
  rw [show (-(1/2 : ℝ)) + 1 = 1/2 by ring]
  rw [← Real.sqrt_eq_rpow]
  ring

/-- **The square of the test function integrates to `2√(T-s)/√π`.**  So the
variance of `Z_T(s,x)` at intensity `v` is `2 v √(T-s)/√π`, which grows like
the square root of the elapsed time. -/
theorem integral_contNoiseTest_sq {s T : ℝ} (hsT : s ≤ T) (x : ℝ) :
    (∫ p : ℝ × ℝ, (contNoiseTest T s x p) ^ 2)
      = 2 * Real.sqrt (T - s) / Real.sqrt Real.pi := by
  have h3 : (∫ t in Set.Ioo s T, (Real.sqrt (Real.pi * (t - s)))⁻¹)
      = 2 * Real.sqrt (T - s) / Real.sqrt Real.pi := integral_inv_sqrt_pi_sub hsT
  have hint : Integrable (fun p : ℝ × ℝ => (contNoiseTest T s x p) ^ 2)
      ((volume : Measure ℝ).prod volume) := by
    have := integrable_contNoiseTest_sq T s x
    rwa [MeasureTheory.Measure.volume_eq_prod] at this
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.integral_prod _ hint]
  have hfun : (fun t : ℝ => ∫ y : ℝ, (contNoiseTest T s x (t, y)) ^ 2)
      = Set.indicator (Set.Ioo s T) (fun t : ℝ => (Real.sqrt (Real.pi * (t - s)))⁻¹) := by
    funext t
    by_cases hc : s < t ∧ t < T
    · have ht : (0 : ℝ) < t - s := sub_pos.mpr hc.1
      have hval : (∫ y : ℝ, (contNoiseTest T s x (t, y)) ^ 2)
          = ∫ y : ℝ, (contHeat (t - s) x y) ^ 2 := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
        simp [contNoiseTest, hc]
      rw [hval, integral_contHeat_sq ht x, Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨hc.1, hc.2⟩)]
    · simp [contNoiseTest, hc, Set.mem_Ioo]
  rw [hfun, MeasureTheory.integral_indicator measurableSet_Ioo, h3]

end LatticeProb.ContinuumStopping

end
