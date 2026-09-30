import Mathlib
import LatticeProb.Walk.LocalCLT
import LatticeProb.Walk.FourierRec
import LatticeProb.Walk.SimpleTransfer
import LatticeProb.Walk.GreenIdentity
import LatticeProb.Walk.Ball
import LatticeProb.Walk.LineKernel

/-!
# The simple random walk on `ℤ^d` in continuous time

`ctHeat d t x = ∏ᵢ lineKernel (t / d) (xᵢ)` is the kernel at time `t` of the simple random
walk on `ℤ^d` that jumps at rate one. The coordinates are independent one-dimensional walks
at rate `1/d` because the Fourier symbol `e^{-t(1 - φ(θ))}` of the Poisson average of the
discrete kernel factorises, `φ(θ) = d⁻¹ ∑ᵢ cos θᵢ`. This module proves that
factorisation (`hasSum_ctHeat`), the resulting representation `G(x) = ∫_0^∞ q_t(x) dt` of
the Green function in dimension `d ≥ 3`, and the small-time bound. Nothing probabilistic
is used: the identities are read off the Fourier integrals.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace LatticeProb.ContinuousTime

variable {d : ℕ}

/-- The continuous-time kernel of the simple random walk on `ℤ^d`, the product of the
one-dimensional kernels at time `t / d`. -/
def ctHeat (d : ℕ) (t : ℝ) (x : Site d) : ℝ := ∏ i, lineKernel (t / d) (x i)

/-- The Fourier representation of the simple random walk kernel in real form:
`p_n(x) = (2π)^{-d} ∫_{[-π,π]^d} cos(θ·x) φ(θ)^n dθ`, the real part of
`LocalCLT.srwHeat_eq_fourier`. -/
theorem srwHeat_eq_integral_cos (hd : 1 ≤ d) (n : ℕ) (x : Site d) :
    srwHeat d n x = (∫ θ in LocalCLT.torusBox d, Real.cos (dotSite θ x) * charFn d θ ^ n)
      / (2 * Real.pi) ^ d := by
  have hre := congrArg Complex.re (LocalCLT.srwHeat_eq_fourier hd n x)
  rw [Complex.ofReal_re] at hre
  rw [hre]
  have hden : (2 * (Real.pi : ℂ)) ^ d = (((2 * Real.pi : ℝ) ^ d : ℝ) : ℂ) := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_pow]
  rw [hden, Complex.div_ofReal_re, ← RCLike.re_to_complex,
    ← integral_re (LocalCLT.fourier_integrand_integrable d n x)]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with θ
  have hchar : (↑(∑ i : Fin d, Real.cos (θ i)) / (d : ℂ))
      = ((charFn d θ : ℝ) : ℂ) := by
    rw [charFn]
    push_cast
    ring
  simp only [RCLike.re_to_complex]
  rw [hchar, ← Complex.ofReal_pow, Complex.re_mul_ofReal, ← cos_dotSite_eq_re_prod θ x]

/-- The continuous-time kernel is the torus integral of the character against
`e^{-t(1 - φ)}`: the symbol factorises over the coordinates, and so does the integral
over the product measure. -/
theorem ctHeat_eq_integral (hd : 1 ≤ d) (t : ℝ) (x : Site d) :
    (ctHeat d t x : ℂ) = (∫ θ in LocalCLT.torusBox d,
        (∏ k, Complex.exp (↑(θ k * ↑(x k)) * Complex.I))
          * Complex.exp (-(t : ℂ) * (1 - ↑(charFn d θ)))) / (2 * ↑Real.pi) ^ d := by
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpoint : ∀ θ : Fin d → ℝ,
      (∏ k, Complex.exp (↑(θ k * ↑(x k)) * Complex.I))
          * Complex.exp (-(t : ℂ) * (1 - ↑(charFn d θ)))
        = ∏ k, lineIntegrand (t / d) (x k) (θ k) := by
    intro θ
    simp only [lineIntegrand, ← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    rw [Finset.sum_add_distrib, add_comm]
    congr 1
    · rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      simp only [charFn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one, Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast,
        Complex.ofReal_cos]
      field_simp
    · exact Finset.sum_congr rfl fun k _ => by push_cast; ring
  simp_rw [hpoint]
  rw [← LocalCLT.torusMeasure_eq_restrict]
  unfold torusMeasure
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (fun k (y : ℝ) => lineIntegrand (t / d) (x k) y)]
  have hone : ∀ k : ℤ, ∫ θ in Set.Icc (-Real.pi) Real.pi, lineIntegrand (t / d) k θ
      = (2 * Real.pi : ℂ) * lineKernel (t / d) k := by
    intro k
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
      (by linarith [Real.pi_pos]), lineKernel_eq_integral, mul_inv_cancel_left₀]
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  simp_rw [hone]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    mul_div_cancel_left₀ _ (pow_ne_zero _ (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))]
  simp [ctHeat]

/-- The real form of `ctHeat_eq_integral`:
`q_t(x) = (2π)^{-d} ∫_{[-π,π]^d} e^{-t(1 - φ(θ))} cos(θ·x) dθ`. -/
theorem ctHeat_eq_integral_cos (hd : 1 ≤ d) (t : ℝ) (x : Site d) :
    ctHeat d t x = (∫ θ in LocalCLT.torusBox d,
        Real.exp (-t * (1 - charFn d θ)) * Real.cos (dotSite θ x)) / (2 * Real.pi) ^ d := by
  have hcont : Continuous fun θ : Fin d → ℝ =>
      (∏ k, Complex.exp (↑(θ k * ↑(x k)) * Complex.I))
      * Complex.exp (-(t : ℂ) * (1 - ↑(charFn d θ))) := by
    unfold charFn
    fun_prop
  have hint : Integrable (fun θ : Fin d → ℝ =>
      (∏ k, Complex.exp (↑(θ k * ↑(x k)) * Complex.I))
        * Complex.exp (-(t : ℂ) * (1 - ↑(charFn d θ))))
      (volume.restrict (LocalCLT.torusBox d)) :=
    hcont.integrableOn_Icc
  have h := congrArg Complex.re (ctHeat_eq_integral hd t x)
  rw [Complex.ofReal_re] at h
  rw [h, show (2 * (Real.pi : ℂ)) ^ d = (((2 * Real.pi) ^ d : ℝ) : ℂ) by push_cast; ring,
    Complex.div_ofReal_re]
  congr 1
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only
  rw [show -(t : ℂ) * (1 - ↑(charFn d θ)) = ((-t * (1 - charFn d θ) : ℝ) : ℂ) by
      push_cast; ring,
    ← Complex.ofReal_exp, Complex.re_mul_ofReal, ← cos_dotSite_eq_re_prod]
  ring

/-- **Poissonisation**: the Poisson average `∑_n e^{-t} tⁿ/n! p_n(x)` of the discrete kernel
is the continuous-time kernel `q_t(x)`, by summing the exponential series of the symbol
under the torus integral. -/
theorem hasSum_ctHeat (hd : 1 ≤ d) (t : ℝ) (x : Site d) :
    HasSum (fun n : ℕ => Real.exp (-t) * t ^ n / n.factorial * srwHeat d n x)
      (ctHeat d t x) := by
  set μ := volume.restrict (LocalCLT.torusBox d) with hμ
  haveI : IsFiniteMeasure μ := by
    rw [hμ]; exact isFiniteMeasure_restrict.mpr (isCompact_Icc.measure_lt_top.ne)
  set χ : (Fin d → ℝ) → ℂ := fun θ =>
    ∏ k, Complex.exp (↑(θ k * ↑(x k)) * Complex.I) with hχdef
  have hχcont : Continuous χ := by rw [hχdef]; fun_prop
  have hχ : ∀ θ, ‖χ θ‖ = 1 := by
    intro θ
    simp only [χ, norm_prod]
    exact Finset.prod_eq_one fun k _ => Complex.norm_exp_ofReal_mul_I _
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hφ : ∀ θ, |charFn d θ| ≤ 1 := by
    intro θ
    rw [charFn, abs_div, abs_of_pos hdpos, div_le_one hdpos]
    calc |∑ i, Real.cos (θ i)| ≤ ∑ i, |Real.cos (θ i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ => Real.abs_cos_le_one _
      _ = d := by simp
  have hφcont : Continuous (charFn d) := by unfold charFn; fun_prop
  set c : ℕ → ℝ := fun n => Real.exp (-t) * t ^ n / n.factorial with hc
  set F : ℕ → (Fin d → ℝ) → ℂ := fun n θ =>
    ((c n * charFn d θ ^ n : ℝ) : ℂ) * χ θ with hF
  have hFint : ∀ n, Integrable (F n) μ := fun n =>
    (by rw [hF]; fun_prop : Continuous (F n)).integrableOn_Icc
  have hFnorm : ∀ n θ, ‖F n θ‖ ≤ |c n| := by
    intro n θ
    rw [hF, norm_mul, hχ, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) (hφ θ))
  have hcabs : Summable fun n => |c n| := by
    have h := (Real.summable_pow_div_factorial |t|).mul_left (Real.exp (-t))
    refine h.congr fun n => ?_
    rw [hc, abs_div, abs_mul, abs_pow, Real.abs_exp, Nat.abs_cast]
    ring
  have hsum : Summable fun n => ∫ θ, ‖F n θ‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun θ => norm_nonneg _)
      (fun n => ?_) (hcabs.mul_right (μ Set.univ).toReal)
    calc ∫ θ, ‖F n θ‖ ∂μ ≤ ∫ _θ, |c n| ∂μ :=
          integral_mono (hFint n).norm (integrable_const _) (hFnorm n)
      _ = |c n| * (μ Set.univ).toReal := by
          rw [integral_const, smul_eq_mul, mul_comm, Measure.real]
  have hHas := hasSum_integral_of_summable_integral_norm hFint hsum
  have hexp : ∀ θ,
      HasSum (fun n => c n * charFn d θ ^ n) (Real.exp (-t * (1 - charFn d θ))) := by
    intro θ
    have h := (Real.exp_eq_exp_ℝ ▸ NormedSpace.expSeries_div_hasSum_exp (t * charFn d θ) :
      HasSum (fun n => (t * charFn d θ) ^ n / n.factorial) (Real.exp (t * charFn d θ)))
    have h2 := h.mul_left (Real.exp (-t))
    rw [← Real.exp_add, show -t + t * charFn d θ = -t * (1 - charFn d θ) by ring] at h2
    refine h2.congr_fun fun n => ?_
    rw [hc, mul_pow]
    ring
  have htsum : ∀ θ,
      ∑' n, F n θ = ((Real.exp (-t * (1 - charFn d θ)) : ℝ) : ℂ) * χ θ := by
    intro θ
    rw [hF, tsum_mul_right, ← Complex.ofReal_tsum, (hexp θ).tsum_eq]
  simp_rw [htsum] at hHas
  have hct := ctHeat_eq_integral hd t x
  have hpi : (2 * (Real.pi : ℂ)) ^ d ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  rw [← Complex.hasSum_ofReal, hct]
  have hmain := hHas.div_const ((2 * (Real.pi : ℂ)) ^ d)
  have hval : (∫ θ in LocalCLT.torusBox d,
      (∏ k, Complex.exp (↑(θ k * ↑(x k)) * Complex.I))
      * Complex.exp (-(t : ℂ) * (1 - ↑(charFn d θ))))
      = ∫ θ, ((Real.exp (-t * (1 - charFn d θ)) : ℝ) : ℂ) * χ θ ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only
    rw [show -(t : ℂ) * (1 - ↑(charFn d θ)) = ((-t * (1 - charFn d θ) : ℝ) : ℂ) by
        push_cast; ring,
      ← Complex.ofReal_exp]
    ring
  rw [hval]
  refine hmain.congr_fun fun n => ?_
  have hn := LocalCLT.srwHeat_eq_fourier hd n x
  push_cast
  rw [hn, mul_div_assoc', ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only [hF, hc, hχdef, charFn]
  push_cast
  ring

/-- In dimension `d ≥ 3` the Green function is the time integral of the continuous-time
kernel, `G(x) = ∫_0^∞ q_t(x) dt`, because each Poisson weight has total mass one. -/
theorem srwGreenInf_eq_integral_ctHeat (hd : 3 ≤ d) (x : Site d) :
    srwGreenInf d x = ∫ t in Set.Ioi 0, ctHeat d t x := by
  have hgamma : ∀ n : ℕ, IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ n) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi 0, Real.exp (-t) * t ^ n = n.factorial := by
    intro n
    have hconv := Real.GammaIntegral_convergent (s := (n : ℝ) + 1) (by positivity)
    have hval := Real.Gamma_eq_integral (s := (n : ℝ) + 1) (by positivity)
    rw [Real.Gamma_nat_eq_factorial] at hval
    have hpow : ∀ t : ℝ, Real.exp (-t) * t ^ ((n : ℝ) + 1 - 1) = Real.exp (-t) * t ^ n := by
      intro t
      rw [add_sub_cancel_right, Real.rpow_natCast]
    simp only [hpow] at hconv hval
    exact ⟨hconv, hval.symm⟩
  set F : ℕ → ℝ → ℝ := fun n t => Real.exp (-t) * t ^ n / n.factorial * srwHeat d n x
    with hF
  have hFint : ∀ n, Integrable (F n) (volume.restrict (Set.Ioi 0)) := by
    intro n
    have h := ((hgamma n).1.div_const (n.factorial : ℝ)).mul_const (srwHeat d n x)
    exact h
  have hFnorm : ∀ n, ∫ t in Set.Ioi 0, ‖F n t‖ = srwHeat d n x := by
    intro n
    have hnn : ∀ t ∈ Set.Ioi (0 : ℝ), ‖F n t‖ = F n t := by
      intro t ht
      rw [Real.norm_eq_abs, abs_of_nonneg]
      have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
      have := srwHeat_nonneg (d := d) n x
      positivity
    rw [setIntegral_congr_fun measurableSet_Ioi hnn, hF]
    simp only
    rw [integral_mul_const, integral_div, (hgamma n).2, div_self (by positivity), one_mul]
  have hsum : Summable fun n => ∫ t in Set.Ioi 0, ‖F n t‖ := by
    simp_rw [hFnorm]
    exact summable_srwHeat (by omega) x
  have h := integral_tsum_of_summable_integral_norm hFint hsum
  have hlhs : ∑' n, ∫ t in Set.Ioi 0, F n t = srwGreenInf d x := by
    rw [srwGreenInf]
    refine tsum_congr fun n => ?_
    rw [← hFnorm n]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg]
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have := srwHeat_nonneg (d := d) n x
    simp only [hF]
    positivity
  rw [← hlhs, h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  exact (hasSum_ctHeat (by omega) t x).tsum_eq

/-- The continuous-time kernel is continuous in the time. -/
theorem continuous_ctHeat (x : Site d) : Continuous fun t => ctHeat d t x := by
  unfold ctHeat
  apply continuous_finsetProd
  intro i _
  exact (continuous_lineKernel (x i)).comp (continuous_id.div_const (d : ℝ))

/-- `cosh (1 / 2) - 1 ≤ 1`. -/
private lemma cosh_half_sub_one_le_one : Real.cosh (1 / 2) - 1 ≤ 1 := by
  have hle : Real.cosh (1 / 2) ≤ Real.cosh 1 := Real.cosh_le_cosh.mpr (by norm_num)
  have hlt : Real.cosh 1 < 2 := by
    rw [Real.cosh_eq]
    have h2 : Real.exp (-1) ≤ 1 := by
      have h := Real.exp_le_exp.mpr (by norm_num : (-1 : ℝ) ≤ 0)
      simpa only [Real.exp_zero] using h
    linarith [Real.exp_one_lt_three, h2]
  linarith

/-- The one-dimensional kernel decays like `exp (-|k| / 2 + s)`. -/
private lemma abs_lineKernel_half_le {s : ℝ} (hs : 0 ≤ s) (k : ℤ) :
    |lineKernel s k| ≤ Real.exp (-|(k : ℝ)| / 2 + s) := by
  have hcosh := cosh_half_sub_one_le_one
  rcases lt_or_ge (k : ℝ) 0 with hneg | hnonneg
  · have hkabs : |(k : ℝ)| = -(k : ℝ) := abs_of_neg hneg
    have hstep : Real.exp (-((-1 / 2 : ℝ) * k) + s * (Real.cosh (-1 / 2) - 1))
        ≤ Real.exp (-|(k : ℝ)| / 2 + s) := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.cosh_neg]
      apply Real.exp_le_exp.mpr
      rw [hkabs]
      nlinarith [hcosh, hs]
    exact (abs_lineKernel_le_exp hs k (-1 / 2)).trans hstep
  · have hkabs : |(k : ℝ)| = (k : ℝ) := abs_of_nonneg hnonneg
    have hstep : Real.exp (-((1 / 2 : ℝ) * k) + s * (Real.cosh (1 / 2) - 1))
        ≤ Real.exp (-|(k : ℝ)| / 2 + s) := by
      apply Real.exp_le_exp.mpr
      rw [hkabs]
      nlinarith [hcosh, hs]
    exact (abs_lineKernel_le_exp hs k (1 / 2)).trans hstep

/-- The Euclidean norm of a site is at most the sum of the absolute values of its
coordinates. -/
private lemma euclidNorm_le_sum_abs (x : Site d) :
    euclidNorm x ≤ ∑ i : Fin d, |(x i : ℝ)| := by
  have hsq : ∑ i : Fin d, ((x i : ℤ) : ℝ) ^ 2 ≤ (∑ i : Fin d, |(x i : ℝ)|) ^ 2 := by
    have h := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := (Finset.univ : Finset (Fin d))) (f := fun i => |(x i : ℝ)|)
      (fun i _ => abs_nonneg _)
    simpa only [sq_abs] using h
  have hnn : (0 : ℝ) ≤ ∑ i : Fin d, |(x i : ℝ)| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  rw [euclidNorm]
  calc Real.sqrt (∑ i : Fin d, ((x i : ℤ) : ℝ) ^ 2)
      ≤ Real.sqrt ((∑ i : Fin d, |(x i : ℝ)|) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ∑ i : Fin d, |(x i : ℝ)| := Real.sqrt_sq hnn

/-- The small-time bound `|q_t(x)| ≤ e^t e^{-|x|/2}`, from the exponential bound on each
coordinate at `Im θ = ±1/2`. -/
theorem abs_ctHeat_le (hd : 1 ≤ d) {t : ℝ} (ht : 0 ≤ t) (x : Site d) :
    |ctHeat d t x| ≤ Real.exp t * Real.exp (-euclidNorm x / 2) := by
  have hdpos_nat : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hdpos_nat
  have hsd : (0 : ℝ) ≤ t / d := div_nonneg ht hdpos.le
  have hsum : ∑ i : Fin d, (-|(x i : ℝ)| / 2 + t / d)
      = -(∑ i : Fin d, |(x i : ℝ)|) / 2 + t := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_neg_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hprod : (∏ i : Fin d, |lineKernel (t / d) (x i)|)
      ≤ ∏ i : Fin d, Real.exp (-|(x i : ℝ)| / 2 + t / d) :=
    Finset.prod_le_prod (fun i _ => abs_nonneg _)
      (fun i _ => abs_lineKernel_half_le hsd (x i))
  calc |ctHeat d t x|
      = |∏ i : Fin d, lineKernel (t / d) (x i)| := by rw [ctHeat]
    _ = ∏ i : Fin d, |lineKernel (t / d) (x i)| := by rw [Finset.abs_prod]
    _ ≤ ∏ i : Fin d, Real.exp (-|(x i : ℝ)| / 2 + t / d) := hprod
    _ = Real.exp (∑ i : Fin d, (-|(x i : ℝ)| / 2 + t / d)) := by rw [Real.exp_sum]
    _ = Real.exp (-(∑ i : Fin d, |(x i : ℝ)|) / 2 + t) := by rw [hsum]
    _ = Real.exp t * Real.exp (-(∑ i : Fin d, |(x i : ℝ)|) / 2) := by
        rw [Real.exp_add]
        ring
    _ ≤ Real.exp t * Real.exp (-euclidNorm x / 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        apply Real.exp_le_exp.mpr
        linarith [euclidNorm_le_sum_abs x]

end LatticeProb.ContinuousTime
