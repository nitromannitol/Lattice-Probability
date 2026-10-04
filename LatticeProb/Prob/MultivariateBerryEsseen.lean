/-
# Multivariate Berry–Esseen: the one-dimensional analytic core

This file starts the discharge of `Sandpile.External.MultivariateBerryEsseen` (Raič,
*Bernoulli* 25 (2019), Theorem 1.1) in the `LatticeProb` library.  The route
(`scratch/pk/mvbe-route.md`) names a strictly nested set of missing lemmas; this file lands the
first bounded one:

* `LatticeProb.norm_exp_mul_I_sub_quadratic_le` — the two-term Taylor bound
  `‖exp (u I) - (1 + u I + (u I)²/2)‖ ≤ |u|³/6` on the imaginary axis, proved from Taylor's
  theorem with the integral remainder.
* `LatticeProb.integrable_pow_of_integrable_abs_three` — a third absolute moment gives
  integrability of the first three monomials.
* `LatticeProb.charFun_third_order_le` (route A1) — for a centred probability law with finite
  third absolute moment, the characteristic function agrees with `1 - Var t²/2` up to
  `|t|³ (∫|z|³)/6`.

Still missing and out of scope here: route A2 (`charFun_exp_sub_le`, `charFun_norm_le_exp`),
A3 (`esseens_smoothing`), A4 (`berryEsseen_oneDim`) and the multivariate assembly C1/D1.  The
frozen Prop in `Divisible-Sandpile-Percolation` is untouched.
-/
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ComplexOrder

namespace LatticeProb

/-- The two-term Taylor bound for the exponential on the imaginary axis:
`‖exp (u I) - (1 + u I + (u I)²/2)‖ ≤ |u|³/6`.

Proved by Taylor's theorem with the integral remainder applied to `s ↦ exp (s · u I)`. -/
theorem norm_exp_mul_I_sub_quadratic_le (u : ℝ) :
    ‖Complex.exp ((u : ℂ) * Complex.I)
        - (1 + (u : ℂ) * Complex.I + ((u : ℂ) * Complex.I) ^ 2 / 2)‖ ≤
      |u| ^ 3 / 6 := by
  set w : ℂ := (u : ℂ) * Complex.I with hw
  have hw_norm : ‖w‖ = |u| := by
    rw [hw, Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  have hlin : ContDiff ℝ ⊤ (fun s : ℝ => (s : ℂ) * w) :=
    Complex.ofRealCLM.contDiff.mul contDiff_const
  have hcd : ContDiff ℝ ⊤ (fun s : ℝ => Complex.exp ((s : ℂ) * w)) := hlin.cexp
  have hf_hasDeriv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * w))
      (w * Complex.exp ((s : ℂ) * w)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * w) w s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const w
    convert h1.cexp using 1
    ring
  have hiter : ∀ k : ℕ, iteratedDeriv k (fun s : ℝ => Complex.exp ((s : ℂ) * w))
      = fun s : ℝ => w ^ k * Complex.exp ((s : ℂ) * w) := by
    intro k
    induction k with
    | zero => funext s; simp [iteratedDeriv_zero]
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      have h : HasDerivAt (fun s : ℝ => w ^ k * Complex.exp ((s : ℂ) * w))
          (w ^ k * (w * Complex.exp ((s : ℂ) * w))) s :=
        (hf_hasDeriv s).const_mul (w ^ k)
      rw [h.deriv]
      ring
  have hcont : ContDiffOn ℝ 3 (fun s : ℝ => Complex.exp ((s : ℂ) * w)) (Set.uIcc (0:ℝ) 1) :=
    hcd.contDiffOn.of_le (by simp)
  have htaylor := taylor_integral_remainder (f := fun s : ℝ => Complex.exp ((s : ℂ) * w))
    (x := 1) (x₀ := 0) (n := 2) hcont
  have hcdAt1 : ContDiffAt ℝ 1 (fun s : ℝ => Complex.exp ((s : ℂ) * w)) 0 :=
    hcd.contDiffAt.of_le (by simp)
  have hiv1 : iteratedDerivWithin 1 (fun s : ℝ => Complex.exp ((s : ℂ) * w))
      (Set.uIcc (0:ℝ) 1) 0 = w := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by norm_num)) hcdAt1
      (by rw [Set.uIcc_of_le (by norm_num)]; exact ⟨le_refl 0, by norm_num⟩)]
    rw [iteratedDeriv_one]
    have h := (hf_hasDeriv 0).deriv
    simpa using h
  have hiv2 : iteratedDerivWithin 2 (fun s : ℝ => Complex.exp ((s : ℂ) * w))
      (Set.uIcc (0:ℝ) 1) 0 = w ^ 2 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by norm_num))
        (hcd.contDiffAt.of_le (by simp))
        (by rw [Set.uIcc_of_le (by norm_num)]; exact ⟨le_refl 0, by norm_num⟩)]
    rw [hiter 2]
    simp
  have hpoly : taylorWithinEval (fun s : ℝ => Complex.exp ((s : ℂ) * w)) 2
      (Set.uIcc (0:ℝ) 1) 0 1 = 1 + w + w ^ 2 / 2 := by
    rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval, hiv1, hiv2]
    norm_num
    ring
  rw [hpoly] at htaylor
  simp only [Complex.ofReal_one, one_mul] at htaylor
  rw [htaylor]
  have hiv3 : ∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖iteratedDerivWithin 3 (fun s : ℝ => Complex.exp ((s : ℂ) * w)) (Set.uIcc (0:ℝ) 1) t‖
        ≤ ‖w‖ ^ 3 := by
    intro t ht
    have ht' : t ∈ Set.uIcc (0:ℝ) 1 := by rwa [Set.uIcc_of_le (by norm_num)]
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by norm_num))
        (hcd.contDiffAt.of_le (by simp)) ht', hiter 3, norm_mul, norm_pow]
    have hexp : ‖Complex.exp ((t : ℂ) * w)‖ = 1 := by
      have htw : (t : ℂ) * w = ((t * u : ℝ) : ℂ) * Complex.I := by rw [hw]; push_cast; ring
      rw [htw, Complex.norm_exp_ofReal_mul_I]
    rw [hexp, mul_one]
  have hnorm : ∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖((1 - t) ^ 2 / (Nat.factorial 2 : ℝ)) •
        iteratedDerivWithin 3 (fun s : ℝ => Complex.exp ((s : ℂ) * w)) (Set.uIcc (0:ℝ) 1) t‖
        ≤ (1 - t) ^ 2 / 2 * ‖w‖ ^ 3 := by
    intro t ht
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have h2 : (Nat.factorial 2 : ℝ) = 2 := by norm_num
    rw [h2]
    exact mul_le_mul_of_nonneg_left (hiv3 t ht) (by positivity)
  calc ‖∫ t in (0:ℝ)..1, ((1 - t) ^ 2 / (Nat.factorial 2 : ℝ)) •
        iteratedDerivWithin 3 (fun s : ℝ => Complex.exp ((s : ℂ) * w)) (Set.uIcc (0:ℝ) 1) t‖
      ≤ ∫ t in (0:ℝ)..1, (1 - t) ^ 2 / 2 * ‖w‖ ^ 3 := by
        apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
        · filter_upwards with t ht
          exact hnorm t (Set.Ioc_subset_Icc_self ht)
        · exact (by fun_prop : Continuous (fun t : ℝ => (1 - t)^2/2 * ‖w‖^3)).intervalIntegrable 0 1
    _ = ‖w‖ ^ 3 / 6 := by
        have hInt : ∫ t in (0:ℝ)..1, (1 - t)^2 / 2 = 1/6 := by
          rw [intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x ^ 2 / 2) 1]
          norm_num
        rw [intervalIntegral.integral_mul_const, hInt]
        ring
    _ = |u| ^ 3 / 6 := by rw [hw_norm]

/-- Integrability of the first three monomials from a third absolute moment. -/
theorem integrable_pow_of_integrable_abs_three {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν) :
    Integrable (fun z : ℝ => z) ν ∧ Integrable (fun z : ℝ => z ^ 2) ν ∧
      Integrable (fun z : ℝ => z ^ 3) ν := by
  have hg : Integrable (fun z : ℝ => (1 : ℝ) + |z| ^ 3) ν :=
    (integrable_const (1:ℝ)).add h3
  have hb1 : ∀ z : ℝ, |z| ≤ 1 + |z| ^ 3 := by
    intro z
    have h0 : (0:ℝ) ≤ |z| := abs_nonneg z
    nlinarith [h0, sq_nonneg (|z|), sq_nonneg (|z| - 1), sq_nonneg (|z| + 1)]
  have hb2 : ∀ z : ℝ, |z| ^ 2 ≤ 1 + |z| ^ 3 := by
    intro z
    have h0 : (0:ℝ) ≤ |z| := abs_nonneg z
    nlinarith [h0, sq_nonneg (|z|), sq_nonneg (|z| - 1)]
  refine ⟨?_, ?_, ?_⟩
  · refine hg.mono' (by fun_prop) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs]
    exact hb1 z
  · refine hg.mono' (by fun_prop) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_pow]
    exact hb2 z
  · refine h3.mono' (by fun_prop) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_pow]

/-- Route A1: for a centred probability law `ν` on `ℝ` with finite third absolute moment, the
characteristic function differs from `1 - Var t²/2` by at most `|t|³ (∫ |z|³)/6`. -/
theorem charFun_third_order_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (h3 : Integrable (fun z => |z| ^ 3) ν) :
    ∀ t : ℝ,
      ‖charFun ν t - (1 - (variance id ν : ℂ) * (t : ℂ) ^ 2 / 2)‖
        ≤ |t| ^ 3 * (∫ z, |z| ^ 3 ∂ν) / 6 := by
  intro t
  have hv : variance id ν = ∫ z, z ^ 2 ∂ν :=
    variance_of_integral_eq_zero measurable_id.aemeasurable hmean
  have hg : Integrable (fun z : ℝ => (1 : ℝ) + |z| ^ 3) ν :=
    (integrable_const (1:ℝ)).add h3
  have hb1 : ∀ z : ℝ, |z| ≤ 1 + |z| ^ 3 := by
    intro z; have h0 : (0:ℝ) ≤ |z| := abs_nonneg z
    nlinarith [h0, sq_nonneg (|z|), sq_nonneg (|z| - 1), sq_nonneg (|z| + 1)]
  have hb2 : ∀ z : ℝ, |z| ^ 2 ≤ 1 + |z| ^ 3 := by
    intro z; have h0 : (0:ℝ) ≤ |z| := abs_nonneg z
    nlinarith [h0, sq_nonneg (|z|), sq_nonneg (|z| - 1)]
  have hexp : Integrable (fun z : ℝ => Complex.exp ((t : ℂ) * (z : ℂ) * Complex.I)) ν := by
    refine (integrable_const (1:ℝ)).mono' (by fun_prop) ?_
    filter_upwards with z
    have h : ‖Complex.exp ((t : ℂ) * (z : ℂ) * Complex.I)‖ = 1 := by
      have h2 : (t : ℂ) * (z : ℂ) * Complex.I = ((t * z : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [h2, Complex.norm_exp_ofReal_mul_I]
    simp [h]
  have hzc : Integrable (fun z : ℝ => (z : ℂ)) ν := by
    refine hg.mono' (by fun_prop) ?_
    filter_upwards with z
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hb1 z
  have hzc2 : Integrable (fun z : ℝ => (z : ℂ) ^ 2) ν := by
    refine hg.mono' (by fun_prop) ?_
    filter_upwards with z
    simpa [norm_pow, Complex.norm_real, Real.norm_eq_abs] using hb2 z
  have hlin : Integrable (fun z : ℝ => (t : ℂ) * (z : ℂ) * Complex.I) ν := by
    rw [show (fun z : ℝ => (t : ℂ) * (z : ℂ) * Complex.I)
        = fun z : ℝ => ((t : ℂ) * Complex.I) * (z : ℂ) by funext z; ring]
    exact hzc.const_mul _
  have hquad : Integrable (fun z : ℝ => ((t : ℂ) * (z : ℂ) * Complex.I) ^ 2 / 2) ν := by
    rw [show (fun z : ℝ => ((t : ℂ) * (z : ℂ) * Complex.I) ^ 2 / 2)
        = fun z : ℝ => (((t : ℂ) * Complex.I) ^ 2 / 2) * (z : ℂ) ^ 2 by funext z; ring]
    exact hzc2.const_mul _
  have hpoly_int : Integrable (fun z : ℝ =>
      (1:ℂ) + (t : ℂ) * (z : ℂ) * Complex.I + ((t : ℂ) * (z : ℂ) * Complex.I) ^ 2 / 2) ν :=
    ((integrable_const (1:ℂ)).add hlin).add hquad
  have hpoly_eq : ∫ z, ((1:ℂ) + (t : ℂ) * (z : ℂ) * Complex.I
      + ((t : ℂ) * (z : ℂ) * Complex.I) ^ 2 / 2) ∂ν
      = 1 - (variance id ν : ℂ) * (t : ℂ) ^ 2 / 2 := by
    rw [hv]
    have hP1 : Integrable (fun z : ℝ => (1:ℂ)) ν := integrable_const _
    have hP12 : Integrable (fun z : ℝ => (1:ℂ) + (t:ℂ)*(z:ℂ)*Complex.I) ν := hP1.add hlin
    rw [integral_add hP12 hquad]
    rw [integral_add hP1 hlin]
    have h1 : ∫ z, (1:ℂ) ∂ν = 1 := by simp
    have h2 : ∫ z, (t : ℂ) * (z : ℂ) * Complex.I ∂ν = 0 := by
      rw [show (fun z : ℝ => (t : ℂ) * (z : ℂ) * Complex.I)
          = fun z : ℝ => ((t : ℂ) * Complex.I) * (z : ℂ) by funext z; ring]
      rw [integral_const_mul]
      have hzint : (∫ z : ℝ, (z : ℂ) ∂ν) = ((∫ z, z ∂ν : ℝ) : ℂ) := integral_ofReal
      rw [hzint, hmean]
      simp
    have h3int : ∫ z, ((t : ℂ) * (z : ℂ) * Complex.I) ^ 2 / 2 ∂ν
        = -((t : ℂ) ^ 2 / 2) * (((∫ z, z ^ 2 ∂ν) : ℝ) : ℂ) := by
      rw [show (fun z : ℝ => ((t : ℂ) * (z : ℂ) * Complex.I) ^ 2 / 2)
          = fun z : ℝ => (((t : ℂ) * Complex.I) ^ 2 / 2) * (z : ℂ) ^ 2 by funext z; ring]
      rw [integral_const_mul]
      have hz2 : ∫ z, (z : ℂ) ^ 2 ∂ν = ((∫ z, z ^ 2 ∂ν : ℝ) : ℂ) := by
        rw [show (fun z : ℝ => (z : ℂ) ^ 2) = fun z : ℝ => ((z ^ 2 : ℝ) : ℂ) by
          funext z; push_cast; ring]
        exact integral_ofReal
      rw [hz2, mul_pow]
      have hI : Complex.I ^ 2 = (-1 : ℂ) := by rw [pow_two, Complex.I_mul_I]
      rw [hI]
      ring
    rw [h1, h2, h3int]
    ring
  rw [charFun_apply_real]
  have hsub : (∫ z, Complex.exp ((t : ℂ) * (z : ℂ) * Complex.I) ∂ν)
        - (1 - (variance id ν : ℂ) * (t : ℂ) ^ 2 / 2)
      = ∫ z, (Complex.exp ((t : ℂ) * (z : ℂ) * Complex.I)
          - ((1:ℂ) + (t : ℂ) * (z : ℂ) * Complex.I + ((t : ℂ) * (z : ℂ) * Complex.I) ^ 2 / 2)) ∂ν := by
    rw [← hpoly_eq, integral_sub hexp hpoly_int]
  rw [hsub]
  have hpoint : ∀ z : ℝ,
      ‖Complex.exp ((t : ℂ) * (z : ℂ) * Complex.I)
          - ((1:ℂ) + (t : ℂ) * (z : ℂ) * Complex.I + ((t : ℂ) * (z : ℂ) * Complex.I) ^ 2 / 2)‖
        ≤ |t * z| ^ 3 / 6 := by
    intro z
    have h := norm_exp_mul_I_sub_quadratic_le (t * z)
    have h2 : ((t * z : ℝ) : ℂ) * Complex.I = (t : ℂ) * (z : ℂ) * Complex.I := by push_cast; ring
    rw [h2] at h
    convert h using 2
  calc ‖∫ z, (Complex.exp ((t : ℂ) * (z : ℂ) * Complex.I)
          - ((1:ℂ) + (t : ℂ) * (z : ℂ) * Complex.I + ((t : ℂ) * (z : ℂ) * Complex.I) ^ 2 / 2)) ∂ν‖
      ≤ ∫ z, ‖Complex.exp ((t : ℂ) * (z : ℂ) * Complex.I)
          - ((1:ℂ) + (t : ℂ) * (z : ℂ) * Complex.I + ((t : ℂ) * (z : ℂ) * Complex.I) ^ 2 / 2)‖ ∂ν :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z, (|t| ^ 3 / 6) * |z| ^ 3 ∂ν := by
        apply integral_mono_ae
        · exact (hexp.sub hpoly_int).norm
        · exact h3.const_mul _
        · filter_upwards with z
          refine le_trans (hpoint z) (le_of_eq ?_)
          rw [abs_mul, mul_pow]
          ring
    _ = |t| ^ 3 / 6 * ∫ z, |z| ^ 3 ∂ν := by
        rw [integral_const_mul]
    _ = |t| ^ 3 * (∫ z, |z| ^ 3 ∂ν) / 6 := by ring

end LatticeProb
