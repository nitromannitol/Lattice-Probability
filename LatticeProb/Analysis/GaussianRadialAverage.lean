import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Gaussian radial averages

The heat kernel `p_{ε²/2}` on the plane is radial, and in polar coordinates about its centre its
radial weight on `(0, ∞)` is the probability density `(2 / ε²) r e^{-r²/ε²}`. Hence the heat-kernel
mollification of a field at a point is the average of the circle averages `F r` about that point
against this density, `(2 / ε²) ∫_0^∞ r F(r) e^{-r²/ε²} dr`. The substitution `r = ε u` turns the
density into the scale-free weight `2 u e^{-u²}`, of total mass `1`. Therefore, for every
constant `c`,

`(2 / ε²) ∫_0^∞ r F(r) e^{-r²/ε²} dr - c = ∫_0^∞ 2 u e^{-u²} (F(ε u) - c) du`.

With `c = F ε` this writes the difference between a heat-kernel mollification and the circle
average at the heat scale as an average of circle-average increments `F(ε u) - F(ε)` across scales.

* `integral_two_mul_exp_neg_sq`: `∫_0^∞ 2 u e^{-u²} du = 1`;
* `integrableOn_gaussRadial_iff`: the two radial integrands are integrable together;
* `gaussRadial_integral_eq`: the change of variables `r = ε u`;
* `gaussRadial_integral_sub_eq`, `gaussRadial_integral_sub_self_eq`: the identity above.
-/

open MeasureTheory Filter Topology Set

namespace LatticeProb.GaussianRadialAverage

/-- The scale-free radial Gaussian weight `u ↦ 2 u e^{-u²}` is integrable on `(0, ∞)`. -/
theorem integrableOn_two_mul_exp_neg_sq :
    IntegrableOn (fun u : ℝ => 2 * u * Real.exp (-u ^ 2)) (Ioi 0) := by
  have h := ((integrable_mul_exp_neg_mul_sq (b := 1) one_pos).const_mul 2).integrableOn
    (s := Ioi (0 : ℝ))
  refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp only [neg_mul, one_mul]
  ring

/-- The scale-free radial Gaussian weight has total mass one: `∫_0^∞ 2 u e^{-u²} du = 1`. -/
theorem integral_two_mul_exp_neg_sq :
    ∫ u in Ioi (0 : ℝ), 2 * u * Real.exp (-u ^ 2) = 1 := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt (fun u : ℝ => -Real.exp (-u ^ 2)) (2 * x * Real.exp (-x ^ 2)) x := by
    intro x _
    have h := ((hasDerivAt_pow 2 x).neg.exp).neg
    convert h using 1
    simp only [Pi.neg_apply]
    push_cast
    ring
  have hlim : Tendsto (fun u : ℝ => -Real.exp (-u ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => -u ^ 2) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero)
    simpa using (Real.tendsto_exp_atBot.comp h1).neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv integrableOn_two_mul_exp_neg_sq hlim]
  simp

/-- Pointwise form of the substitution `r = ε u` in the radial Gaussian integrand. -/
theorem gaussRadial_integrand_eq (F : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    2 * u * Real.exp (-u ^ 2) * F (ε * u) =
      2 / ε * ((ε * u) * F (ε * u) * Real.exp (-(ε * u) ^ 2 / ε ^ 2)) := by
  have hε0 : ε ≠ 0 := hε.ne'
  have hexp : -(ε * u) ^ 2 / ε ^ 2 = -u ^ 2 := by
    rw [mul_pow, neg_div, mul_div_cancel_left₀ _ (pow_ne_zero 2 hε0)]
  have hc : 2 / ε * ε = 2 := div_mul_cancel₀ 2 hε0
  rw [hexp]
  linear_combination (-(u * F (ε * u) * Real.exp (-u ^ 2))) * hc

/-- The radial integrand at scale `ε` is integrable on `(0, ∞)` if and only if its rescaled
version against the weight `2 u e^{-u²}` is. -/
theorem integrableOn_gaussRadial_iff (F : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun u : ℝ => 2 * u * Real.exp (-u ^ 2) * F (ε * u)) (Ioi 0) ↔
      IntegrableOn (fun r : ℝ => r * F r * Real.exp (-r ^ 2 / ε ^ 2)) (Ioi 0) := by
  have h := integrableOn_Ioi_comp_mul_left_iff
    (fun r : ℝ => r * F r * Real.exp (-r ^ 2 / ε ^ 2)) 0 hε
  rw [mul_zero] at h
  rw [← h, show (fun u : ℝ => 2 * u * Real.exp (-u ^ 2) * F (ε * u)) =
      fun u : ℝ => 2 / ε * ((ε * u) * F (ε * u) * Real.exp (-(ε * u) ^ 2 / ε ^ 2)) from
    funext (gaussRadial_integrand_eq F hε)]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.2 (by positivity)) _

/-- **Change of variables `r = ε u`** in the radial heat-kernel integral:
`(2 / ε²) ∫_0^∞ r F(r) e^{-r²/ε²} dr = ∫_0^∞ 2 u e^{-u²} F(ε u) du`. -/
theorem gaussRadial_integral_eq (F : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    2 / ε ^ 2 * (∫ r in Ioi (0 : ℝ), r * F r * Real.exp (-r ^ 2 / ε ^ 2)) =
      ∫ u in Ioi (0 : ℝ), 2 * u * Real.exp (-u ^ 2) * F (ε * u) := by
  have h := integral_comp_mul_left_Ioi
    (fun r : ℝ => r * F r * Real.exp (-r ^ 2 / ε ^ 2)) 0 hε
  rw [mul_zero, smul_eq_mul] at h
  rw [integral_congr_ae (ae_of_all _ (gaussRadial_integrand_eq F hε)), integral_const_mul, h]
  ring

/-- **Radial Gaussian average minus a constant.** If the radial integrand is integrable, then for
every constant `c`,
`(2 / ε²) ∫_0^∞ r F(r) e^{-r²/ε²} dr - c = ∫_0^∞ 2 u e^{-u²} (F(ε u) - c) du`. -/
theorem gaussRadial_integral_sub_eq (F : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hF : IntegrableOn (fun r : ℝ => r * F r * Real.exp (-r ^ 2 / ε ^ 2)) (Ioi 0)) (c : ℝ) :
    2 / ε ^ 2 * (∫ r in Ioi (0 : ℝ), r * F r * Real.exp (-r ^ 2 / ε ^ 2)) - c =
      ∫ u in Ioi (0 : ℝ), 2 * u * Real.exp (-u ^ 2) * (F (ε * u) - c) := by
  have h1 := (integrableOn_gaussRadial_iff F hε).2 hF
  have h2 := integrableOn_two_mul_exp_neg_sq.const_mul c
  have e : ∀ u : ℝ, 2 * u * Real.exp (-u ^ 2) * (F (ε * u) - c) =
      2 * u * Real.exp (-u ^ 2) * F (ε * u) - c * (2 * u * Real.exp (-u ^ 2)) :=
    fun u => by ring
  rw [integral_congr_ae (ae_of_all _ e), integral_sub h1 h2, integral_const_mul,
    integral_two_mul_exp_neg_sq, gaussRadial_integral_eq F hε, mul_one]

/-- **Heat-kernel average minus the value at the heat scale**: with `c = F ε`,
`(2 / ε²) ∫_0^∞ r F(r) e^{-r²/ε²} dr - F(ε) = ∫_0^∞ 2 u e^{-u²} (F(ε u) - F(ε)) du`. -/
theorem gaussRadial_integral_sub_self_eq (F : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hF : IntegrableOn (fun r : ℝ => r * F r * Real.exp (-r ^ 2 / ε ^ 2)) (Ioi 0)) :
    2 / ε ^ 2 * (∫ r in Ioi (0 : ℝ), r * F r * Real.exp (-r ^ 2 / ε ^ 2)) - F ε =
      ∫ u in Ioi (0 : ℝ), 2 * u * Real.exp (-u ^ 2) * (F (ε * u) - F ε) :=
  gaussRadial_integral_sub_eq F hε hF (F ε)

end LatticeProb.GaussianRadialAverage
