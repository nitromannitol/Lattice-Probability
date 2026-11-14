import LatticeProb.Prob.BrownianMarginalDensity

/-!
# Time integrals of the Brownian heat kernel

For the heat kernel `p_t(x, y) = brownianHeatKernel d t x y` of the motion with generator
`Δ / (2 d)`, this file computes the time integrals that give the Green function of a ball.
Write `q_N(a, y) = ∫₀^N p_t(a, y) dt`.

* `LatticeProb.integral_brownianHeatKernel_three`: in dimension three,
  `∫₀^∞ p_t(x, y) dt = 3 / (2 π ‖x - y‖)` for `x ≠ y`. The substitution `t = 1 / s` turns the
  integral into `(2 π / 3) ^ (-3 / 2) ∫₀^∞ s ^ (-1 / 2) e ^ (-3 ‖x - y‖² s / 2) ds`, a Gamma
  integral with `Γ(1 / 2) = √π`.
* `LatticeProb.tendsto_greenTime_sub_two`: in dimension two, `q_N(a, y)` diverges, but
  `q_N(a, y) - q_N(b, y)` tends to `(2 / π) log (‖b - y‖ / ‖a - y‖)`. The substitution
  `t = ‖a - y‖² s` gives `q_N(a, y) = π⁻¹ ∫₀^{N / ‖a - y‖²} e ^ (-1 / s) s⁻¹ ds`
  (`LatticeProb.intervalIntegral_brownianHeatKernel_two`), so the difference is the integral of
  `e ^ (-1 / s) s⁻¹` between `N / ‖b - y‖²` and `N / ‖a - y‖²`; it differs from the integral of
  `s⁻¹` over the same interval by at most a constant times `1 / N`.

## Bounds for the limit `N → ∞`

The occupation identity for the exit time `τ` of a ball, truncated at a time `N`, involves
`q_N(x, y) - E[1{τ < N} q_{N - τ}(B_τ, y)]`. The following bounds control its limit as `N → ∞`.

* `LatticeProb.brownianHeatKernel_le`: the bound
  `p_t(x, y) ≤ (2 π ‖x - y‖² / d) ^ (-d / 2) e ^ (-d / 2)`, uniform in `t > 0`, and its consequence
  `LatticeProb.intervalIntegral_brownianHeatKernel_le`, which bounds `q_N - q_{N - τ}` by `τ` times
  this constant.
* `LatticeProb.intervalIntegral_brownianHeatKernel_two_le`: in dimension two,
  `q_N(a, y) ≤ π⁻¹ log (1 + N / ‖a - y‖²)`, for the event `τ ≥ N`.
* `LatticeProb.abs_intervalIntegral_brownianHeatKernel_two_sub_le`: in dimension two,
  `|q_N(a, y) - q_N(b, y)| ≤ (2 / π) |log (‖b - y‖ / ‖a - y‖)|` for every `N > 0`, the domination
  for `q_N(x, y) - q_N(B_τ, y)`.
* `LatticeProb.tendsto_intervalIntegral_brownianHeatKernel_three`: in dimension three,
  `q_N(x, y) → 3 / (2 π ‖x - y‖)`.
-/

open MeasureTheory Filter Topology Set
open scoped Interval

noncomputable section

namespace LatticeProb

variable {d : ℕ}

theorem brownianHeatKernel_nonneg {t : ℝ} (ht : 0 ≤ t) (x y : EuclideanSpace ℝ (Fin d)) :
    0 ≤ brownianHeatKernel d t x y := by
  unfold brownianHeatKernel
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le

theorem measurable_brownianHeatKernel (x y : EuclideanSpace ℝ (Fin d)) :
    Measurable fun t => brownianHeatKernel d t x y := by
  unfold brownianHeatKernel
  fun_prop

/-- The heat kernel at two distinct points is bounded uniformly in time: the maximum of
`t ↦ p_t(x, y)` is attained at `t = ‖x - y‖² / d`. -/
theorem brownianHeatKernel_le (hd : 1 ≤ d) {x y : EuclideanSpace ℝ (Fin d)} (hxy : x ≠ y)
    {t : ℝ} (ht : 0 < t) :
    brownianHeatKernel d t x y ≤
      (2 * Real.pi * ‖x - y‖ ^ 2 / d) ^ (-(d : ℝ) / 2) * Real.exp (-(d : ℝ) / 2) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hr : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  unfold brownianHeatKernel
  generalize ‖x - y‖ = r at hr ⊢
  have hkpos : 0 < (d : ℝ) / 2 := by positivity
  have hwpos : 0 < r ^ 2 / t := by positivity
  have hC : 0 ≤ 2 * Real.pi * r ^ 2 / d := by positivity
  have hbase : 2 * Real.pi * t / d = (2 * Real.pi * r ^ 2 / d) * (r ^ 2 / t)⁻¹ := by
    field_simp
  have hpow : (2 * Real.pi * t / d) ^ (-(d : ℝ) / 2) =
      (2 * Real.pi * r ^ 2 / d) ^ (-(d : ℝ) / 2) * (r ^ 2 / t) ^ ((d : ℝ) / 2) := by
    rw [hbase, Real.mul_rpow hC (inv_nonneg.2 hwpos.le), Real.inv_rpow hwpos.le, neg_div,
      Real.rpow_neg hwpos.le, inv_inv]
  have hexp : -(d : ℝ) * r ^ 2 / (2 * t) = -((d : ℝ) / 2 * (r ^ 2 / t)) := by ring
  have hwk : (r ^ 2 / t) ^ ((d : ℝ) / 2) ≤ Real.exp ((r ^ 2 / t - 1) * ((d : ℝ) / 2)) := by
    rw [Real.exp_mul]
    exact Real.rpow_le_rpow hwpos.le (by linarith [Real.add_one_le_exp (r ^ 2 / t - 1)])
      hkpos.le
  rw [hpow, hexp, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hC _)
  calc (r ^ 2 / t) ^ ((d : ℝ) / 2) * Real.exp (-((d : ℝ) / 2 * (r ^ 2 / t)))
      ≤ Real.exp ((r ^ 2 / t - 1) * ((d : ℝ) / 2)) * Real.exp (-((d : ℝ) / 2 * (r ^ 2 / t))) :=
        mul_le_mul_of_nonneg_right hwk (Real.exp_pos _).le
    _ = Real.exp (-(d : ℝ) / 2) := by rw [← Real.exp_add]; ring_nf

theorem intervalIntegrable_brownianHeatKernel (hd : 1 ≤ d) {x y : EuclideanSpace ℝ (Fin d)}
    (hxy : x ≠ y) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    IntervalIntegrable (fun t => brownianHeatKernel d t x y) volume u v := by
  refine (intervalIntegrable_const (c := (2 * Real.pi * ‖x - y‖ ^ 2 / d) ^ (-(d : ℝ) / 2) *
    Real.exp (-(d : ℝ) / 2))).mono_fun' (measurable_brownianHeatKernel x y).aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_uIoc).mono fun t ht => ?_
  dsimp only
  have ht0 : 0 < t := (le_min hu hv).trans_lt ht.1
  rw [Real.norm_of_nonneg (brownianHeatKernel_nonneg ht0.le x y)]
  exact brownianHeatKernel_le hd hxy ht0

/-- The time integral of the heat kernel over `[u, v] ⊆ [0, ∞)` is at most `v - u` times the
uniform bound of `LatticeProb.brownianHeatKernel_le`. -/
theorem intervalIntegral_brownianHeatKernel_le (hd : 1 ≤ d) {x y : EuclideanSpace ℝ (Fin d)}
    (hxy : x ≠ y) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    ∫ t in u..v, brownianHeatKernel d t x y ≤
      (v - u) * ((2 * Real.pi * ‖x - y‖ ^ 2 / d) ^ (-(d : ℝ) / 2) * Real.exp (-(d : ℝ) / 2)) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := v)
    (f := fun t => brownianHeatKernel d t x y) fun t ht => by
      have ht0 : 0 < t := (le_min hu (hu.trans huv)).trans_lt ht.1
      rw [Real.norm_of_nonneg (brownianHeatKernel_nonneg ht0.le x y)]
      exact brownianHeatKernel_le hd hxy ht0
  rw [abs_of_nonneg (sub_nonneg.2 huv), mul_comm] at h
  exact (Real.le_norm_self _).trans h

/-! ### Dimension three -/

/-- In dimension three, `∫₀^∞ p_t(x, y) dt = 3 / (2 π ‖x - y‖)`. -/
theorem integral_brownianHeatKernel_three {x y : EuclideanSpace ℝ (Fin 3)} (hxy : x ≠ y) :
    ∫ t in Set.Ioi (0 : ℝ), brownianHeatKernel 3 t x y = 3 / (2 * Real.pi * ‖x - y‖) := by
  have hr : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hcpos : (0 : ℝ) < 2 * Real.pi / 3 := by positivity
  have hapos : (0 : ℝ) < 3 * ‖x - y‖ ^ 2 / 2 := by positivity
  have key : ∀ s ∈ Ioi (0 : ℝ),
      (|(-1 : ℝ)| * s ^ ((-1 : ℝ) - 1)) • brownianHeatKernel 3 (s ^ (-1 : ℝ)) x y =
        (2 * Real.pi / 3) ^ (-(3 : ℝ) / 2) *
          (s ^ (-(1 : ℝ) / 2) * Real.exp (-(3 * ‖x - y‖ ^ 2 / 2) * s ^ (1 : ℝ))) := by
    intro s hs
    have hs : 0 < s := hs
    unfold brownianHeatKernel
    rw [Real.rpow_neg_one, Real.rpow_one, smul_eq_mul]
    push_cast
    have e1 : (2 * Real.pi * s⁻¹ / 3) ^ (-(3 : ℝ) / 2) =
        (2 * Real.pi / 3) ^ (-(3 : ℝ) / 2) * s ^ ((3 : ℝ) / 2) := by
      rw [show 2 * Real.pi * s⁻¹ / 3 = 2 * Real.pi / 3 * s⁻¹ by ring,
        Real.mul_rpow hcpos.le (inv_nonneg.2 hs.le), Real.inv_rpow hs.le, neg_div,
        Real.rpow_neg hs.le, inv_inv]
    have e2 : -3 * ‖x - y‖ ^ 2 / (2 * s⁻¹) = -(3 * ‖x - y‖ ^ 2 / 2) * s := by
      field_simp
    have e3 : s ^ ((-1 : ℝ) - 1) * s ^ ((3 : ℝ) / 2) = s ^ (-(1 : ℝ) / 2) := by
      rw [← Real.rpow_add hs]; norm_num
    rw [e1, e2, abs_neg, abs_one, one_mul, ← e3]
    ring
  rw [← integral_comp_rpow_Ioi (fun t => brownianHeatKernel 3 t x y) (p := -1) (by norm_num),
    setIntegral_congr_fun measurableSet_Ioi key, integral_const_mul,
    integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hapos]
  have hG : Real.Gamma ((-(1 : ℝ) / 2 + 1) / 1) = √Real.pi := by
    rw [← Real.Gamma_one_half_eq]; norm_num
  have h1 : (3 * ‖x - y‖ ^ 2 / 2) ^ (-(-(1 : ℝ) / 2 + 1) / 1) = (√(3 * ‖x - y‖ ^ 2 / 2))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hapos.le]; norm_num
  have h2 : (2 * Real.pi / 3) ^ (-(3 : ℝ) / 2) = (2 * Real.pi / 3 * √(2 * Real.pi / 3))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hcpos.le (by norm_num), ← Real.rpow_neg hcpos.le]
    norm_num
  have hca : √(2 * Real.pi / 3) * √(3 * ‖x - y‖ ^ 2 / 2) = √Real.pi * ‖x - y‖ := by
    rw [← Real.sqrt_mul hcpos.le, show 2 * Real.pi / 3 * (3 * ‖x - y‖ ^ 2 / 2) =
      Real.pi * ‖x - y‖ ^ 2 by ring, Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hr.le]
  have hpi : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  rw [hG, h1, h2]
  calc (2 * Real.pi / 3 * √(2 * Real.pi / 3))⁻¹ *
        ((√(3 * ‖x - y‖ ^ 2 / 2))⁻¹ * (1 / 1) * √Real.pi)
      = (2 * Real.pi / 3)⁻¹ * √Real.pi *
          (√(2 * Real.pi / 3) * √(3 * ‖x - y‖ ^ 2 / 2))⁻¹ := by
        rw [mul_inv, mul_inv]; ring
    _ = 3 / (2 * Real.pi * ‖x - y‖) := by
        rw [hca]; field_simp

theorem integrableOn_brownianHeatKernel_three {x y : EuclideanSpace ℝ (Fin 3)} (hxy : x ≠ y) :
    IntegrableOn (fun t => brownianHeatKernel 3 t x y) (Ioi 0) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_brownianHeatKernel_three hxy]
  have hr : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  positivity

theorem tendsto_intervalIntegral_brownianHeatKernel_three {x y : EuclideanSpace ℝ (Fin 3)}
    (hxy : x ≠ y) :
    Tendsto (fun N : ℝ => ∫ t in (0 : ℝ)..N, brownianHeatKernel 3 t x y) atTop
      (𝓝 (3 / (2 * Real.pi * ‖x - y‖))) := by
  rw [← integral_brownianHeatKernel_three hxy]
  exact intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_brownianHeatKernel_three hxy)
    tendsto_id

/-! ### Dimension two -/

private lemma exp_neg_inv_mul_inv_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ Real.exp (-s⁻¹) * s⁻¹ := by
  positivity

private lemma exp_neg_inv_mul_inv_le_inv_one_add {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (-s⁻¹) * s⁻¹ ≤ (1 + s)⁻¹ := by
  rcases hs.eq_or_lt with rfl | hs
  · simp
  have h1 : s⁻¹ + 1 ≤ Real.exp s⁻¹ := Real.add_one_le_exp _
  have h2 : (0 : ℝ) < 1 + s := by linarith
  rw [Real.exp_neg, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos _)]
  calc s⁻¹ = (1 + s)⁻¹ * (s⁻¹ + 1) := by field_simp
    _ ≤ (1 + s)⁻¹ * Real.exp s⁻¹ := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 h2.le)

private lemma exp_neg_inv_mul_inv_le_inv {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (-s⁻¹) * s⁻¹ ≤ s⁻¹ :=
  mul_le_of_le_one_left (inv_nonneg.2 hs)
    (Real.exp_le_one_iff.2 (neg_nonpos.2 (inv_nonneg.2 hs)))

private lemma abs_exp_neg_inv_mul_inv_sub_inv_le {s : ℝ} (hs : 0 < s) :
    |Real.exp (-s⁻¹) * s⁻¹ - s⁻¹| ≤ s⁻¹ * s⁻¹ := by
  have h0 : 0 < s⁻¹ := inv_pos.2 hs
  have h1 : -s⁻¹ + 1 ≤ Real.exp (-s⁻¹) := Real.add_one_le_exp _
  have h2 : Real.exp (-s⁻¹) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 h0.le)
  rw [abs_of_nonpos (by nlinarith)]
  nlinarith

private lemma measurable_exp_neg_inv_mul_inv : Measurable fun s : ℝ => Real.exp (-s⁻¹) * s⁻¹ := by
  fun_prop

private lemma intervalIntegrable_exp_neg_inv_mul_inv {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    IntervalIntegrable (fun s : ℝ => Real.exp (-s⁻¹) * s⁻¹) volume u v := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    measurable_exp_neg_inv_mul_inv.aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_uIoc).mono fun s hs => ?_
  dsimp only
  have hs0 : 0 ≤ s := (le_min hu hv).trans hs.1.le
  rw [Real.norm_of_nonneg (exp_neg_inv_mul_inv_nonneg hs0)]
  exact (exp_neg_inv_mul_inv_le_inv_one_add hs0).trans (inv_le_one_of_one_le₀ (by linarith))

private lemma intervalIntegrable_inv_of_pos {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable (fun s : ℝ => s⁻¹) volume u v :=
  (continuousOn_inv₀.mono fun _ hs => (lt_inf_iff.2 ⟨hu, hv⟩).trans_le hs.1 |>.ne').intervalIntegrable

/-- In dimension two, the substitution `t = ‖a - y‖² s` gives
`q_N(a, y) = π⁻¹ ∫₀^{N / ‖a - y‖²} e ^ (-1 / s) s⁻¹ ds`. -/
theorem intervalIntegral_brownianHeatKernel_two {a y : EuclideanSpace ℝ (Fin 2)} (hay : a ≠ y)
    (N : ℝ) :
    ∫ t in (0 : ℝ)..N, brownianHeatKernel 2 t a y =
      Real.pi⁻¹ * ∫ s in (0 : ℝ)..N / ‖a - y‖ ^ 2, Real.exp (-s⁻¹) * s⁻¹ := by
  have hr : 0 < ‖a - y‖ ^ 2 := by
    have := norm_pos_iff.2 (sub_ne_zero.2 hay)
    positivity
  have hpt : ∀ t : ℝ, brownianHeatKernel 2 t a y = Real.pi⁻¹ * ((‖a - y‖ ^ 2)⁻¹ *
      (Real.exp (-((‖a - y‖ ^ 2)⁻¹ * t)⁻¹) * ((‖a - y‖ ^ 2)⁻¹ * t)⁻¹)) := by
    intro t
    unfold brownianHeatKernel
    push_cast
    generalize ‖a - y‖ ^ 2 = c at hr ⊢
    rw [show -(2 : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one, mul_inv c⁻¹ t, inv_inv,
      show -2 * c / (2 * t) = -(c * t⁻¹) by ring]
    calc (2 * Real.pi * t / 2)⁻¹ * Real.exp (-(c * t⁻¹))
        = Real.pi⁻¹ * (Real.exp (-(c * t⁻¹)) * t⁻¹) := by ring
      _ = Real.pi⁻¹ * (c⁻¹ * (Real.exp (-(c * t⁻¹)) * (c * t⁻¹))) := by
        congr 1
        calc Real.exp (-(c * t⁻¹)) * t⁻¹ = (c⁻¹ * c) * (Real.exp (-(c * t⁻¹)) * t⁻¹) := by
              rw [inv_mul_cancel₀ hr.ne', one_mul]
          _ = c⁻¹ * (Real.exp (-(c * t⁻¹)) * (c * t⁻¹)) := by ring
  have hsub := intervalIntegral.integral_comp_mul_left (a := 0) (b := N)
    (fun s : ℝ => Real.exp (-s⁻¹) * s⁻¹) (inv_ne_zero hr.ne')
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hsub, smul_eq_mul,
    inv_inv, ← mul_assoc (‖a - y‖ ^ 2)⁻¹, inv_mul_cancel₀ hr.ne', one_mul, mul_zero,
    inv_mul_eq_div (‖a - y‖ ^ 2) N]

/-- In dimension two, `q_N(a, y) ≤ π⁻¹ log (1 + N / ‖a - y‖²)` for `N ≥ 0`. -/
theorem intervalIntegral_brownianHeatKernel_two_le {a y : EuclideanSpace ℝ (Fin 2)} (hay : a ≠ y)
    {N : ℝ} (hN : 0 ≤ N) :
    ∫ t in (0 : ℝ)..N, brownianHeatKernel 2 t a y ≤
      Real.pi⁻¹ * Real.log (1 + N / ‖a - y‖ ^ 2) := by
  rw [intervalIntegral_brownianHeatKernel_two hay]
  have hX : 0 ≤ N / ‖a - y‖ ^ 2 := by positivity
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 Real.pi_pos.le)
  have hinv : IntervalIntegrable (fun s : ℝ => (1 + s)⁻¹) volume 0 (N / ‖a - y‖ ^ 2) := by
    refine (ContinuousOn.inv₀ (by fun_prop) fun s hs => ?_).intervalIntegrable
    rw [Set.uIcc_of_le hX] at hs
    linarith [hs.1]
  have hshift := intervalIntegral.integral_comp_add_left (a := 0) (b := N / ‖a - y‖ ^ 2)
    (fun s : ℝ => s⁻¹) 1
  simp only [add_zero] at hshift
  calc ∫ s in (0 : ℝ)..N / ‖a - y‖ ^ 2, Real.exp (-s⁻¹) * s⁻¹
      ≤ ∫ s in (0 : ℝ)..N / ‖a - y‖ ^ 2, (1 + s)⁻¹ :=
        intervalIntegral.integral_mono_on hX (intervalIntegrable_exp_neg_inv_mul_inv le_rfl hX)
          hinv fun s hs => exp_neg_inv_mul_inv_le_inv_one_add hs.1
    _ = Real.log (1 + N / ‖a - y‖ ^ 2) := by
        rw [hshift, integral_inv_of_pos one_pos (by linarith), div_one]

private lemma intervalIntegral_brownianHeatKernel_two_sub {a b y : EuclideanSpace ℝ (Fin 2)}
    (hay : a ≠ y) (hby : b ≠ y) {N : ℝ} (hN : 0 < N) :
    (∫ t in (0 : ℝ)..N, brownianHeatKernel 2 t a y) - ∫ t in (0 : ℝ)..N, brownianHeatKernel 2 t b y =
      Real.pi⁻¹ * ∫ s in N / ‖b - y‖ ^ 2..N / ‖a - y‖ ^ 2, Real.exp (-s⁻¹) * s⁻¹ := by
  rw [intervalIntegral_brownianHeatKernel_two hay, intervalIntegral_brownianHeatKernel_two hby,
    ← mul_sub, intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_exp_neg_inv_mul_inv le_rfl (by positivity))
      (intervalIntegrable_exp_neg_inv_mul_inv le_rfl (by positivity))]

private lemma two_div_pi_mul_log_eq {a b y : EuclideanSpace ℝ (Fin 2)} (hay : a ≠ y) (hby : b ≠ y)
    {N : ℝ} (hN : 0 < N) :
    2 / Real.pi * Real.log (‖b - y‖ / ‖a - y‖) =
      Real.pi⁻¹ * ∫ s in N / ‖b - y‖ ^ 2..N / ‖a - y‖ ^ 2, s⁻¹ := by
  have ha : 0 < ‖a - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hay)
  have hb : 0 < ‖b - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hby)
  rw [integral_inv_of_pos (div_pos hN (pow_pos hb 2)) (div_pos hN (pow_pos ha 2)),
    show N / ‖a - y‖ ^ 2 / (N / ‖b - y‖ ^ 2) = (‖b - y‖ / ‖a - y‖) ^ 2 by field_simp,
    Real.log_pow]
  push_cast
  ring

/-- In dimension two, `|q_N(a, y) - q_N(b, y)| ≤ (2 / π) |log (‖b - y‖ / ‖a - y‖)|` for every
`N > 0`. -/
theorem abs_intervalIntegral_brownianHeatKernel_two_sub_le {a b y : EuclideanSpace ℝ (Fin 2)}
    (hay : a ≠ y) (hby : b ≠ y) {N : ℝ} (hN : 0 < N) :
    |(∫ t in (0 : ℝ)..N, brownianHeatKernel 2 t a y) -
        ∫ t in (0 : ℝ)..N, brownianHeatKernel 2 t b y| ≤
      2 / Real.pi * |Real.log (‖b - y‖ / ‖a - y‖)| := by
  have ha : 0 < ‖a - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hay)
  have hb : 0 < ‖b - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hby)
  have hA : 0 < N / ‖a - y‖ ^ 2 := div_pos hN (pow_pos ha 2)
  have hB : 0 < N / ‖b - y‖ ^ 2 := div_pos hN (pow_pos hb 2)
  have hpi : 0 < Real.pi⁻¹ := inv_pos.2 Real.pi_pos
  have hpos : ∀ s ∈ Ι (N / ‖b - y‖ ^ 2) (N / ‖a - y‖ ^ 2), 0 < s :=
    fun s hs => (lt_min hB hA).trans hs.1
  rw [intervalIntegral_brownianHeatKernel_two_sub hay hby hN, abs_mul, abs_of_pos hpi,
    ← abs_of_pos (div_pos two_pos Real.pi_pos), ← abs_mul, two_div_pi_mul_log_eq hay hby hN,
    abs_mul, abs_of_pos hpi]
  refine mul_le_mul_of_nonneg_left ?_ hpi.le
  rw [intervalIntegral.abs_integral_eq_abs_integral_uIoc,
    intervalIntegral.abs_integral_eq_abs_integral_uIoc,
    abs_of_nonneg (setIntegral_nonneg measurableSet_uIoc
      fun s hs => exp_neg_inv_mul_inv_nonneg (hpos s hs).le),
    abs_of_nonneg (setIntegral_nonneg measurableSet_uIoc fun s hs => (inv_pos.2 (hpos s hs)).le)]
  exact setIntegral_mono_on (intervalIntegrable_exp_neg_inv_mul_inv hB.le hA.le).def'
    (intervalIntegrable_inv_of_pos hB hA).def' measurableSet_uIoc
    fun s hs => exp_neg_inv_mul_inv_le_inv (hpos s hs).le

/-- In dimension two, `q_N(a, y) - q_N(b, y) → (2 / π) log (‖b - y‖ / ‖a - y‖)` as `N → ∞`. -/
theorem tendsto_greenTime_sub_two {a b y : EuclideanSpace ℝ (Fin 2)} (hay : a ≠ y) (hby : b ≠ y) :
    Tendsto (fun N : ℝ => (∫ t in (0 : ℝ)..N, brownianHeatKernel 2 t a y) -
        ∫ t in (0 : ℝ)..N, brownianHeatKernel 2 t b y)
      atTop (𝓝 (2 / Real.pi * Real.log (‖b - y‖ / ‖a - y‖))) := by
  have ha : 0 < ‖a - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hay)
  have hb : 0 < ‖b - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hby)
  have hS : 0 < ‖a - y‖ ^ 2 + ‖b - y‖ ^ 2 := by positivity
  have hpi : 0 < Real.pi⁻¹ := inv_pos.2 Real.pi_pos
  set K : ℝ := Real.pi⁻¹ * ((‖a - y‖ ^ 2 + ‖b - y‖ ^ 2) ^ 2 *
    |(‖a - y‖ ^ 2)⁻¹ - (‖b - y‖ ^ 2)⁻¹|) with hK
  have hK0 : Tendsto (fun N : ℝ => K / N) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hK0
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hA : 0 < N / ‖a - y‖ ^ 2 := div_pos hN (pow_pos ha 2)
  have hB : 0 < N / ‖b - y‖ ^ 2 := div_pos hN (pow_pos hb 2)
  have hs0 : 0 < N / (‖a - y‖ ^ 2 + ‖b - y‖ ^ 2) := div_pos hN hS
  have hlow : ∀ s ∈ Ι (N / ‖b - y‖ ^ 2) (N / ‖a - y‖ ^ 2),
      N / (‖a - y‖ ^ 2 + ‖b - y‖ ^ 2) ≤ s := fun s hs =>
    (le_min (div_le_div_of_nonneg_left hN.le (pow_pos hb 2) (by nlinarith))
      (div_le_div_of_nonneg_left hN.le (pow_pos ha 2) (by nlinarith))).trans hs.1.le
  have hbound : ∀ s ∈ Ι (N / ‖b - y‖ ^ 2) (N / ‖a - y‖ ^ 2),
      ‖Real.exp (-s⁻¹) * s⁻¹ - s⁻¹‖ ≤
        (N / (‖a - y‖ ^ 2 + ‖b - y‖ ^ 2))⁻¹ * (N / (‖a - y‖ ^ 2 + ‖b - y‖ ^ 2))⁻¹ := by
    intro s hs
    have hsl := hlow s hs
    have hinv := inv_anti₀ hs0 hsl
    rw [Real.norm_eq_abs]
    exact (abs_exp_neg_inv_mul_inv_sub_inv_le (hs0.trans_le hsl)).trans
      (mul_le_mul hinv hinv (inv_nonneg.2 (hs0.trans_le hsl).le) (inv_nonneg.2 hs0.le))
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [intervalIntegral_brownianHeatKernel_two_sub hay hby hN, two_div_pi_mul_log_eq hay hby hN,
    ← mul_sub, ← intervalIntegral.integral_sub
      (intervalIntegrable_exp_neg_inv_mul_inv hB.le hA.le) (intervalIntegrable_inv_of_pos hB hA),
    norm_mul, Real.norm_of_nonneg hpi.le]
  refine (mul_le_mul_of_nonneg_left hint hpi.le).trans_eq ?_
  rw [show N / ‖a - y‖ ^ 2 - N / ‖b - y‖ ^ 2 = N * ((‖a - y‖ ^ 2)⁻¹ - (‖b - y‖ ^ 2)⁻¹) by ring,
    abs_mul, abs_of_pos hN, hK]
  field_simp

end LatticeProb
