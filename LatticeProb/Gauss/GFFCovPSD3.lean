import Mathlib

/-!
# Frullani and Gaussian identities for the whole-plane covariance

The following identities are proved in pure analysis:

* `frullani_exp`, `frullani_norm`: the Frullani integral `∫_{s>0} s⁻¹ (e^{-A s} - e^{-s}) ds = -log A` for `A > 0`
  (Mathlib `integral_Ioi_eq`, `Mathlib/Analysis/SpecialFunctions/FrullaniIntegral.lean`), with its absolute version;
* `integral_gauss`, `integral_gauss_mul`: the Gaussian integrals on `ℂ` (Mathlib `GaussianFourier`), and the
  convolution identity `exp(-s|x-y|²) = (4s/π) ∫_w exp(-2s|x-w|²) exp(-2s|y-w|²) dw` (Duplantier-Sheffield heat-kernel
  representation of the logarithm, Armitage-Gardiner Ch. 3 for the kernel `-log|x-y|`).
-/

open MeasureTheory Set Filter Topology
open scoped Real

namespace LatticeProb.Gauss.GFFCovPSD

/-- The elementary bound `|e^u - e^v| ≤ |u - v| e^{max u v}`, from `e^t ≥ 1 + t`. -/
lemma abs_exp_sub_exp_le (u v : ℝ) :
    |Real.exp u - Real.exp v| ≤ |u - v| * Real.exp (max u v) := by
  have key : ∀ a b : ℝ, a ≤ b → |Real.exp a - Real.exp b| ≤ |a - b| * Real.exp (max a b) := by
    intro a b h
    have h1 : Real.exp a = Real.exp b * Real.exp (a - b) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : 1 + (a - b) ≤ Real.exp (a - b) := by linarith [Real.add_one_le_exp (a - b)]
    have hb : 0 < Real.exp b := Real.exp_pos b
    have e1 : |Real.exp a - Real.exp b| = Real.exp b - Real.exp a := by
      rw [abs_of_nonpos (by linarith [Real.exp_le_exp.mpr h])]; ring
    have e2 : |a - b| = b - a := by rw [abs_of_nonpos (by linarith)]; ring
    rw [e1, e2, max_eq_right h]
    nlinarith [mul_le_mul_of_nonneg_left h2 hb.le]
  rcases le_total u v with h | h
  · exact key u v h
  · have := key v u h
    rwa [abs_sub_comm (Real.exp v) (Real.exp u), abs_sub_comm v u, max_comm] at this

/-- The Frullani integrand `s⁻¹ (e^{-A s} - e^{-s})` is integrable on `(0, ∞)` for `A > 0`. -/
lemma frullani_integrableOn {A : ℝ} (hA : 0 < A) :
    IntegrableOn (fun s : ℝ => s⁻¹ • (Real.exp (-(A * s)) - Real.exp (-(1 * s)))) (Ioi 0) := by
  have hm : 0 < min A 1 := lt_min hA one_pos
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hm).const_mul |A - 1|) ?_ ?_
  · exact (measurable_inv.smul ((Real.measurable_exp.comp (measurable_const.mul measurable_id).neg).sub
      (Real.measurable_exp.comp (measurable_const.mul measurable_id).neg))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : 0 < s := hs
    have hmx : max (-(A * s)) (-(1 * s)) = -(min A 1 * s) := by
      rcases le_total A 1 with h | h
      · rw [min_eq_left h, max_eq_left (show -(1 * s) ≤ -(A * s) by nlinarith)]
      · rw [min_eq_right h, max_eq_right (show -(A * s) ≤ -(1 * s) by nlinarith)]
    have hab : |-(A * s) - -(1 * s)| = |A - 1| * s := by
      rw [show -(A * s) - -(1 * s) = -((A - 1) * s) by ring, abs_neg, abs_mul, abs_of_pos hs']
    have hb := abs_exp_sub_exp_le (-(A * s)) (-(1 * s))
    rw [hmx, hab] at hb
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs']
    calc s⁻¹ * |Real.exp (-(A * s)) - Real.exp (-(1 * s))|
        ≤ s⁻¹ * (|A - 1| * s * Real.exp (-(min A 1 * s))) :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hs'.le)
      _ = |A - 1| * Real.exp (-min A 1 * s) := by rw [neg_mul]; field_simp

/-- The Frullani integral: `∫_{s>0} s⁻¹ (e^{-A s} - e^{-s}) ds = -log A` for `A > 0`. -/
theorem frullani_exp {A : ℝ} (hA : 0 < A) :
    ∫ s in Ioi (0 : ℝ), s⁻¹ • (Real.exp (-(A * s)) - Real.exp (-(1 * s))) = -Real.log A := by
  have hL : Tendsto (fun u : ℝ => Real.exp (-u)) (𝓝[>] 0) (𝓝 1) := by
    have h0 : Tendsto (fun u : ℝ => Real.exp (-u)) (𝓝 0) (𝓝 (Real.exp (-0))) :=
      (Real.continuous_exp.comp continuous_neg).tendsto 0
    rw [neg_zero, Real.exp_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have h := Frullani.integral_Ioi_eq (f := fun u : ℝ => Real.exp (-u)) (a := A) (b := 1) (L := 1) (R := 0)
    ((Continuous.locallyIntegrable (f := fun u : ℝ => Real.exp (-u)) (by fun_prop)).locallyIntegrableOn _)
    hA one_pos hL hR
    (frullani_integrableOn hA)
  simpa [one_div, Real.log_inv, smul_eq_mul] using h

/-- The absolute Frullani integral: `∫_{s>0} |s⁻¹ (e^{-A s} - e^{-s})| ds = |log A|` for `A > 0`
(the integrand has constant sign in `s`). -/
theorem frullani_norm {A : ℝ} (hA : 0 < A) :
    ∫ s in Ioi (0 : ℝ), ‖s⁻¹ • (Real.exp (-(A * s)) - Real.exp (-(1 * s)))‖ = |Real.log A| := by
  rcases le_total A 1 with h1 | h1
  · rw [abs_of_nonpos (Real.log_nonpos hA.le h1), ← frullani_exp hA]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs' : 0 < s := hs
    have hnn : 0 ≤ s⁻¹ • (Real.exp (-(A * s)) - Real.exp (-(1 * s))) :=
      smul_nonneg (inv_nonneg.mpr hs'.le)
        (sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith)))
    exact Real.norm_of_nonneg hnn
  · rw [abs_of_nonneg (Real.log_nonneg h1), ← neg_neg (Real.log A), ← frullani_exp hA, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs' : 0 < s := hs
    have hnp : s⁻¹ • (Real.exp (-(A * s)) - Real.exp (-(1 * s))) ≤ 0 :=
      smul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hs'.le)
        (sub_nonpos.mpr (Real.exp_le_exp.mpr (by nlinarith)))
    exact Real.norm_of_nonpos hnp

/-- The Gaussian `e^{-b|v|²}` on `ℂ` is integrable, for `b > 0`. -/
lemma integrable_gauss_zero {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : ℂ => Real.exp (-b * ‖v‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (b : ℂ))
    (by simpa using hb) 0 0
  refine Integrable.congr h.re (ae_of_all _ fun v => ?_)
  have e : (-(b : ℂ) * (‖v‖ : ℂ) ^ 2 + 0 * ((inner ℝ (0 : ℂ) v : ℝ) : ℂ)) = ((-b * ‖v‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  show (Complex.exp (-(b : ℂ) * (‖v‖ : ℂ) ^ 2 + 0 * ((inner ℝ (0 : ℂ) v : ℝ) : ℂ))).re = Real.exp (-b * ‖v‖ ^ 2)
  rw [e, Complex.exp_ofReal_re]

/-- The translated Gaussian `w ↦ e^{-b|x-w|²}` is integrable on `ℂ`, for `b > 0`. -/
lemma integrable_gauss {b : ℝ} (hb : 0 < b) (x : ℂ) :
    Integrable (fun w : ℂ => Real.exp (-b * ‖x - w‖ ^ 2)) :=
  (integrable_gauss_zero hb).comp_sub_left x

/-- The Gaussian integral on `ℂ`: `∫_w e^{-b|x-w|²} dw = π / b` for `b > 0`. -/
lemma integral_gauss {b : ℝ} (hb : 0 < b) (x : ℂ) :
    ∫ w : ℂ, Real.exp (-b * ‖x - w‖ ^ 2) = π / b := by
  have h := integral_sub_left_eq_self (fun v : ℂ => Real.exp (-b * ‖v‖ ^ 2)) (μ := volume) x
  rw [h, GaussianFourier.integral_rexp_neg_mul_sq_norm hb, Complex.finrank_real_complex]
  norm_num

/-- The Gaussian convolution identity on `ℂ`:
`∫_w e^{-2s|x-w|²} e^{-2s|y-w|²} dw = (π / 4s) e^{-s|x-y|²}` for `s > 0`. -/
lemma integral_gauss_mul {s : ℝ} (hs : 0 < s) (x y : ℂ) :
    ∫ w : ℂ, Real.exp (-(2 * s) * ‖x - w‖ ^ 2) * Real.exp (-(2 * s) * ‖y - w‖ ^ 2)
      = π / (4 * s) * Real.exp (-(s * ‖x - y‖ ^ 2)) := by
  have hn : ∀ w : ℂ, ‖x - w‖ ^ 2 + ‖y - w‖ ^ 2 = 2 * ‖(x + y) / 2 - w‖ ^ 2 + ‖x - y‖ ^ 2 / 2 := by
    intro w
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.div_ofNat_re, Complex.div_ofNat_im]
    ring
  have key : ∀ w : ℂ, Real.exp (-(2 * s) * ‖x - w‖ ^ 2) * Real.exp (-(2 * s) * ‖y - w‖ ^ 2)
      = Real.exp (-(s * ‖x - y‖ ^ 2)) * Real.exp (-(4 * s) * ‖(x + y) / 2 - w‖ ^ 2) := by
    intro w
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    linear_combination (-(2 * s)) * hn w
  rw [integral_congr_ae (ae_of_all _ key), integral_const_mul, integral_gauss (by positivity) ((x + y) / 2)]
  ring

end LatticeProb.Gauss.GFFCovPSD
