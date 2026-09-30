/-
Generic even-moment bounds for real Gaussian random variables, the first ingredient of a
maximal-inequality route for a continuum Gaussian random field.

Every statement is about an abstract Gaussian law `ProbabilityTheory.gaussianReal 0 v` or an
abstract random variable whose law is such a Gaussian, on an abstract probability space.

Main results:

- `pow_le_factorial_mul_exp`: the elementary real-analysis fact `t^n ≤ n! · exp t` for `t ≥ 0`,
  from the nonnegativity of every term of the exponential's power series.
- `integral_pow_two_mul_gaussianReal_le`: for `Y` with law `gaussianReal 0 v`, the even-moment
  bound `E[Y^(2m)] ≤ √2 · m! · 4^m · v^m`, proved by dominating the Gaussian density's own
  exponential tail by a wider Gaussian (via `pow_le_factorial_mul_exp` applied to
  `t = x²/(4v)`) and evaluating the wider Gaussian integral in closed form
  (`Real.integral_gaussian`).  This constant is not sharp (the sharp value is the double
  factorial `(2m-1)!! · v^m`) but every constant here depends only on `m`, which is all a
  Kolmogorov-Chentsov application needs.
- `integrable_pow_two_mul_gaussianReal`: the companion integrability fact, from Mathlib's own
  `ProbabilityTheory.memLp_id_gaussianReal` (a real Gaussian has moments of every order).
- `integrable_pow_two_mul_of_map_eq_gaussianReal` / `integral_pow_two_mul_le_of_map_eq_gaussianReal`:
  the same two facts transported along a pushforward, for any random variable `W` on any
  probability space with `μ.map W = gaussianReal 0 v`.

Moved from Parking-Sharpness.
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace LatticeProb.Scaling.GaussianMoments

/-- **`t^n ≤ n! · exp t` for `t ≥ 0`.**  Every term of the exponential's power series at a
nonnegative argument is nonnegative, so the `n`-th term alone is bounded by the whole sum. -/
theorem pow_le_factorial_mul_exp {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ n ≤ (n.factorial : ℝ) * Real.exp x := by
  have hseries : Real.exp x = ∑' k : ℕ, x ^ k / (k.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ]
    exact congrFun NormedSpace.exp_eq_tsum_div x
  have hsummable : Summable (fun k : ℕ => x ^ k / (k.factorial : ℝ)) :=
    NormedSpace.expSeries_div_summable x
  have hterm_le : x ^ n / (n.factorial : ℝ) ≤ ∑' k : ℕ, x ^ k / (k.factorial : ℝ) := by
    apply hsummable.le_tsum
    intro j _
    exact div_nonneg (pow_nonneg hx j) (Nat.cast_nonneg _)
  rw [← hseries] at hterm_le
  rwa [div_le_iff₀ (by positivity : (0:ℝ) < (n.factorial:ℝ)), mul_comm] at hterm_le

/-- **The `2m`-th moment of a centered Gaussian is `O_m(v^m)`.**  `E[Y^(2m)] ≤ √2·m!·4^m·v^m`
for `Y ~ gaussianReal 0 v`, with a constant depending only on `m` (not sharp; sharp is the
double factorial `(2m-1)!!·v^m`). -/
theorem integral_pow_two_mul_gaussianReal_le (v : NNReal) (m : ℕ) :
    ∫ x : ℝ, x ^ (2 * m) ∂(gaussianReal 0 v)
      ≤ Real.sqrt 2 * (m.factorial : ℝ) * 4 ^ m * (v : ℝ) ^ m := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv
    rw [gaussianReal_zero_var]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp
    · have h2m : 0 < 2 * m := by omega
      simp [zero_pow h2m.ne']
      positivity
  · have hvpos : (0:ℝ) < (v:ℝ) := by
      have := (NNReal.coe_ne_zero).mpr hv
      positivity
    rw [integral_gaussianReal_eq_integral_smul hv]
    have hbound : ∀ x : ℝ, gaussianPDFReal 0 v x • x ^ (2 * m)
        ≤ ((m.factorial:ℝ) * (4*(v:ℝ))^m * (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹) *
          Real.exp (-(1/(4*(v:ℝ))) * x^2) := by
      intro x
      have hstep1 : x ^ (2*m) ≤ (m.factorial:ℝ) * (4*(v:ℝ))^m * Real.exp ((1/(4*(v:ℝ))) * x^2) := by
        have ht0 : (0:ℝ) ≤ (1/(4*(v:ℝ))) * x^2 := by positivity
        have hkey := pow_le_factorial_mul_exp ht0 m
        have heq : ((1/(4*(v:ℝ))) * x^2) ^ m = x ^ (2*m) / (4*(v:ℝ))^m := by
          rw [one_div, inv_mul_eq_div, div_pow, pow_mul]
        rw [heq] at hkey
        rw [div_le_iff₀ (by positivity : (0:ℝ) < (4*(v:ℝ))^m)] at hkey
        calc x ^ (2*m) ≤ (m.factorial:ℝ) * Real.exp ((1/(4*(v:ℝ))) * x^2) * (4*(v:ℝ))^m := hkey
          _ = (m.factorial:ℝ) * (4*(v:ℝ))^m * Real.exp ((1/(4*(v:ℝ))) * x^2) := by ring
      simp only [smul_eq_mul, gaussianPDFReal_def, sub_zero]
      have hexp_nonneg : (0:ℝ) ≤ Real.exp (-(x)^2/(2*(v:ℝ))) := (Real.exp_pos _).le
      have hpdf_nonneg : (0:ℝ) ≤ (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹ := by positivity
      calc (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹ * Real.exp (-(x)^2/(2*(v:ℝ))) * x ^ (2*m)
          ≤ (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹ * Real.exp (-(x)^2/(2*(v:ℝ))) *
              ((m.factorial:ℝ) * (4*(v:ℝ))^m * Real.exp ((1/(4*(v:ℝ))) * x^2)) := by
            apply mul_le_mul_of_nonneg_left hstep1
            exact mul_nonneg hpdf_nonneg hexp_nonneg
        _ = ((m.factorial:ℝ) * (4*(v:ℝ))^m * (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹) *
              (Real.exp (-(x)^2/(2*(v:ℝ))) * Real.exp ((1/(4*(v:ℝ))) * x^2)) := by ring
        _ = ((m.factorial:ℝ) * (4*(v:ℝ))^m * (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹) *
              Real.exp (-(x)^2/(2*(v:ℝ)) + (1/(4*(v:ℝ))) * x^2) := by
            rw [← Real.exp_add]
        _ = ((m.factorial:ℝ) * (4*(v:ℝ))^m * (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹) *
              Real.exp (-(1/(4*(v:ℝ))) * x^2) := by
            congr 2
            field_simp
            ring
    have hintegrable : Integrable (fun x : ℝ =>
        ((m.factorial:ℝ) * (4*(v:ℝ))^m * (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹) *
          Real.exp (-(1/(4*(v:ℝ))) * x^2)) volume := by
      apply Integrable.const_mul
      exact integrable_exp_neg_mul_sq (by positivity)
    have hnonneg : 0 ≤ᵐ[volume] fun x : ℝ => gaussianPDFReal 0 v x • x ^ (2 * m) := by
      filter_upwards with x
      exact mul_nonneg (gaussianPDFReal_nonneg _ _ _)
        (by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) m)
    have hmono := integral_mono_of_nonneg hnonneg hintegrable (ae_of_all volume hbound)
    refine hmono.trans_eq ?_
    rw [integral_const_mul, integral_gaussian]
    have hpi_v_pos : (0:ℝ) < 2 * Real.pi * (v:ℝ) := by positivity
    have hpiv : Real.pi / (1 / (4 * (v:ℝ))) = 2 * (2 * Real.pi * (v:ℝ)) := by
      rw [div_div_eq_mul_div, div_one]; ring
    have hsqrt4piv : Real.sqrt (Real.pi / (1 / (4 * (v:ℝ)))) = Real.sqrt 2 * Real.sqrt (2 * Real.pi * (v:ℝ)) := by
      rw [hpiv, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [hsqrt4piv]
    have hne : Real.sqrt (2 * Real.pi * (v:ℝ)) ≠ 0 := by positivity
    field_simp
    ring

/-- **Every even moment of a real Gaussian is integrable**, from Mathlib's own
`ProbabilityTheory.memLp_id_gaussianReal` (a Gaussian has moments of every order). -/
theorem integrable_pow_two_mul_gaussianReal (v : NNReal) (m : ℕ) :
    Integrable (fun x : ℝ => x ^ (2 * m)) (gaussianReal 0 v) := by
  have h := memLp_id_gaussianReal (μ := (0:ℝ)) (v := v) (2 * m : ℕ)
  have h2 := h.integrable_norm_rpow' (μ := gaussianReal 0 v)
  simp only [id, ENNReal.coe_natCast, ENNReal.toReal_natCast] at h2
  have hfe : (fun x : ℝ => ‖x‖ ^ ((2 * m:ℕ):ℝ)) = fun x : ℝ => x ^ (2 * m) := by
    funext x
    rw [Real.norm_eq_abs, Real.rpow_natCast, ← abs_pow,
      abs_of_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) m)]
  rwa [hfe] at h2

/-- **Transport of integrability along a pushforward**: for any random variable `W` on any
probability space whose law is `gaussianReal 0 v`, `W^(2m)` is integrable. -/
theorem integrable_pow_two_mul_of_map_eq_gaussianReal {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} {W : Ω → ℝ} {v : NNReal} (hW : μ.map W = gaussianReal 0 v)
    (hWmeas : AEMeasurable W μ) (m : ℕ) :
    Integrable (fun ω => (W ω) ^ (2 * m)) μ := by
  have hg : AEStronglyMeasurable (fun x : ℝ => x ^ (2 * m)) (μ.map W) := by
    rw [hW]; exact (integrable_pow_two_mul_gaussianReal v m).aestronglyMeasurable
  exact (integrable_map_measure hg hWmeas).mp (hW ▸ integrable_pow_two_mul_gaussianReal v m)

/-- **Transport of the even-moment bound along a pushforward**: for any random variable `W` on
any probability space whose law is `gaussianReal 0 v`, `E[W^(2m)] ≤ √2·m!·4^m·v^m`. -/
theorem integral_pow_two_mul_le_of_map_eq_gaussianReal {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} {W : Ω → ℝ} {v : NNReal} (hW : μ.map W = gaussianReal 0 v)
    (hWmeas : AEMeasurable W μ) (m : ℕ) :
    ∫ ω, (W ω) ^ (2 * m) ∂μ ≤ Real.sqrt 2 * (m.factorial : ℝ) * 4 ^ m * (v : ℝ) ^ m := by
  have hg : AEStronglyMeasurable (fun x : ℝ => x ^ (2 * m)) (μ.map W) := by
    rw [hW]; exact (integrable_pow_two_mul_gaussianReal v m).aestronglyMeasurable
  rw [← integral_map hWmeas hg, hW]
  exact integral_pow_two_mul_gaussianReal_le v m

end LatticeProb.Scaling.GaussianMoments
