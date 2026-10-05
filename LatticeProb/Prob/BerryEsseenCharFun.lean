/-
# Multivariate Berry–Esseen: per-summand characteristic-function estimates

This file is route A2 of the multivariate Berry–Esseen chain (`scratch/pk/mvbe-route.md`).  For a
centred probability law `ν` on `ℝ` with finite third absolute moment, write `σ² = variance id ν`,
`ρ = ∫ |z|³ dν` and `φ = charFun ν`.  On top of the third-order Taylor bound
`LatticeProb.charFun_third_order_le` it proves four single-summand estimates:

* `LatticeProb.variance_rpow_three_halves_le` — Lyapunov: `σ³ ≤ ρ`.
* `LatticeProb.charFun_norm_le_of_sq_le` — `‖φ t‖ ≤ 1 - σ²t²/2 + ρ|t|³/6` when `σ² t² ≤ 2`.
* `LatticeProb.charFun_norm_le_exp_of_sq_le` — `‖φ t‖ ≤ exp (-σ²t²/2 + ρ|t|³/6)` when `σ² t² ≤ 2`.
* `LatticeProb.charFun_sub_exp_le` — `‖φ t - exp (-σ²t²/2)‖ ≤ ρ|t|³/6 + σ⁴t⁴/8` for all `t`.

The restriction `σ² t² ≤ 2` is needed because `‖1 - σ²t²/2‖` equals `1 - σ²t²/2` only there.  The
estimates for sums of independent summands (which carry the factor `exp (-σ²t²/8)`) are separate.
-/
import Mathlib
import LatticeProb.Prob.MultivariateBerryEsseen

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- Elementary bound `exp (-y) ≤ 1 - y + y²/2` for `y ≥ 0`, from
`1 + y + y²/2 ≤ exp y` and `(1 - y + y²/2)(1 + y + y²/2) = 1 + y⁴/4 ≥ 1`. -/
theorem exp_neg_le_one_sub_add_sq_div_two {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-y) ≤ 1 - y + y ^ 2 / 2 := by
  have hq : 1 + y + y ^ 2 / 2 ≤ Real.exp y := Real.quadratic_le_exp_of_nonneg hy
  have hpos : 0 < 1 + y + y ^ 2 / 2 := by positivity
  have hexp : 0 < Real.exp y := Real.exp_pos y
  have hone : Real.exp (-y) * Real.exp y = 1 := by
    rw [← Real.exp_add]; simp
  have hbig : 0 < 1 - y + y ^ 2 / 2 := by nlinarith [sq_nonneg (y - 1)]
  have hprod : 1 ≤ (1 - y + y ^ 2 / 2) * (1 + y + y ^ 2 / 2) := by
    nlinarith [sq_nonneg (y ^ 2)]
  have hle : (1 - y + y ^ 2 / 2) * (1 + y + y ^ 2 / 2) ≤ (1 - y + y ^ 2 / 2) * Real.exp y :=
    mul_le_mul_of_nonneg_left hq hbig.le
  by_contra hcon
  have hcon' := not_le.mp hcon
  have h2 : (1 - y + y ^ 2 / 2) * Real.exp y < Real.exp (-y) * Real.exp y :=
    mul_lt_mul_of_pos_right hcon' hexp
  linarith

/-- Lyapunov's inequality for a centred probability law with finite third absolute moment:
`(variance id ν) ^ (3/2) ≤ ∫ |z|³ dν`.

Proved from the pointwise bound `|z|³ ≥ s³ + (3/2) s (z² - s²)` (tangent line of `u ↦ u^{3/2}`),
with `s = √(variance id ν)`, integrated against `ν`. -/
theorem variance_rpow_three_halves_le {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν) :
    (variance id ν) ^ ((3 : ℝ) / 2) ≤ ∫ z, |z| ^ 3 ∂ν := by
  have hv : variance id ν = ∫ z, z ^ 2 ∂ν :=
    variance_of_integral_eq_zero measurable_id.aemeasurable hmean
  obtain ⟨-, h2, -⟩ := integrable_pow_of_integrable_abs_three h3
  set s : ℝ := Real.sqrt (variance id ν) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = variance id ν := Real.sq_sqrt (variance_nonneg _ _)
  have hrpow : (variance id ν) ^ ((3 : ℝ) / 2) = s ^ 3 := by
    rw [Real.rpow_div_two_eq_sqrt _ (variance_nonneg _ _), ← hs]
    exact_mod_cast Real.rpow_natCast s 3
  rw [hrpow]
  have hpoint : ∀ z : ℝ, s ^ 3 + 3 / 2 * s * (z ^ 2 - s ^ 2) ≤ |z| ^ 3 := by
    intro z
    have hz : |z| ^ 2 = z ^ 2 := sq_abs z
    have ha : 0 ≤ |z| := abs_nonneg z
    have hkey : 0 ≤ (|z| - s) ^ 2 * (|z| + s / 2) := by positivity
    nlinarith [hkey, hz]
  have hsub : Integrable (fun z : ℝ => z ^ 2 - s ^ 2) ν := h2.sub (integrable_const _)
  have hmul : Integrable (fun z : ℝ => 3 / 2 * s * (z ^ 2 - s ^ 2)) ν := hsub.const_mul _
  have hint_l : Integrable (fun z : ℝ => s ^ 3 + 3 / 2 * s * (z ^ 2 - s ^ 2)) ν :=
    (integrable_const _).add hmul
  calc s ^ 3 = ∫ z, (s ^ 3 + 3 / 2 * s * (z ^ 2 - s ^ 2)) ∂ν := by
        rw [integral_add (integrable_const _) hmul, integral_const_mul,
          integral_sub h2 (integrable_const _), ← hv, hsq]
        simp
    _ ≤ ∫ z, |z| ^ 3 ∂ν := integral_mono hint_l h3 hpoint

/-- For `σ² t² ≤ 2`, the modulus of the characteristic function of a centred probability law with
finite third absolute moment satisfies `‖φ t‖ ≤ 1 - σ²t²/2 + ρ|t|³/6`. -/
theorem charFun_norm_le_of_sq_le {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν) (t : ℝ)
    (ht : variance id ν * t ^ 2 ≤ 2) :
    ‖charFun ν t‖ ≤ 1 - variance id ν * t ^ 2 / 2 + (∫ z, |z| ^ 3 ∂ν) * |t| ^ 3 / 6 := by
  have hA1 := charFun_third_order_le ν hmean h3 t
  have hnorm : ‖(1 - (variance id ν : ℂ) * (t : ℂ) ^ 2 / 2 : ℂ)‖ =
      1 - variance id ν * t ^ 2 / 2 := by
    have hcast : (1 - (variance id ν : ℂ) * (t : ℂ) ^ 2 / 2 : ℂ) =
        ((1 - variance id ν * t ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have htri := norm_sub_norm_le (charFun ν t) (1 - (variance id ν : ℂ) * (t : ℂ) ^ 2 / 2)
  rw [hnorm] at htri
  have : |t| ^ 3 * (∫ z, |z| ^ 3 ∂ν) / 6 = (∫ z, |z| ^ 3 ∂ν) * |t| ^ 3 / 6 := by ring
  linarith

/-- For `σ² t² ≤ 2`, `‖φ t‖ ≤ exp (-σ²t²/2 + ρ|t|³/6)` for a centred probability law with finite
third absolute moment. -/
theorem charFun_norm_le_exp_of_sq_le {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν) (t : ℝ)
    (ht : variance id ν * t ^ 2 ≤ 2) :
    ‖charFun ν t‖ ≤
      Real.exp (-(variance id ν * t ^ 2 / 2) + (∫ z, |z| ^ 3 ∂ν) * |t| ^ 3 / 6) := by
  refine (charFun_norm_le_of_sq_le hmean h3 t ht).trans ?_
  have := Real.add_one_le_exp (-(variance id ν * t ^ 2 / 2) + (∫ z, |z| ^ 3 ∂ν) * |t| ^ 3 / 6)
  linarith

/-- Comparison of the characteristic function of a centred probability law with finite third
absolute moment with the Gaussian one, for every `t`:
`‖φ t - exp (-σ²t²/2)‖ ≤ ρ|t|³/6 + σ⁴t⁴/8`. -/
theorem charFun_sub_exp_le {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν) (t : ℝ) :
    ‖charFun ν t - Complex.exp (-((variance id ν * t ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      (∫ z, |z| ^ 3 ∂ν) * |t| ^ 3 / 6 + (variance id ν) ^ 2 * t ^ 4 / 8 := by
  set y : ℝ := variance id ν * t ^ 2 / 2 with hy
  have hy0 : 0 ≤ y := by
    have := variance_nonneg id ν
    positivity
  have hA1 := charFun_third_order_le ν hmean h3 t
  have hcast : (1 - (variance id ν : ℂ) * (t : ℂ) ^ 2 / 2 : ℂ) = ((1 - y : ℝ) : ℂ) := by
    rw [hy]; push_cast; ring
  rw [hcast] at hA1
  have hsecond : ‖((1 - y : ℝ) : ℂ) - Complex.exp (-(y : ℂ))‖ ≤ y ^ 2 / 2 := by
    have h1 : ((1 - y : ℝ) : ℂ) - Complex.exp (-(y : ℂ)) = ((1 - y - Real.exp (-y) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]; push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
    have hlo : 1 - y ≤ Real.exp (-y) := by
      have := Real.add_one_le_exp (-y)
      linarith
    have hhi := exp_neg_le_one_sub_add_sq_div_two hy0
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hsq : y ^ 2 / 2 = (variance id ν) ^ 2 * t ^ 4 / 8 := by
    rw [hy]; ring
  have htri := norm_sub_le_norm_sub_add_norm_sub (charFun ν t) ((1 - y : ℝ) : ℂ)
    (Complex.exp (-(y : ℂ)))
  have : |t| ^ 3 * (∫ z, |z| ^ 3 ∂ν) / 6 = (∫ z, |z| ^ 3 ∂ν) * |t| ^ 3 / 6 := by ring
  linarith

end LatticeProb
