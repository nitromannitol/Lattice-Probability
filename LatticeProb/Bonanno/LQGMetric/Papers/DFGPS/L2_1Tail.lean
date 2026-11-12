/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_1Tail at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.1: the Gaussian tail estimate of the polar formula

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:726–733: from
(eqn-localized-compare-pt) `|h*_ε(z) − ĥ*_ε(z)| ≤ (2/ε²) ∫_{ε^{1/2}/2}^∞ r |h_r(z)| e^{−r²/ε²} dr`
and Lemma 2.2 (with `ζ = 1/2`: `|h_r(z)| ≤ C max{A log(1/r), log r, 1}`), the right side "tends to
zero exponentially fast as `ε → 0`".

`abs_polar_tail_le`: for any `F` with `|F(r)| ≤ C max{A log(1/r), (log r)^{1/2+1/2}, 1}` and any
weight `w ∈ [0, 1]` vanishing on `(0, √ε/2]` (in the application `w = 1 − ψ_ε`), for `ε ∈ (0, 1]`,
`|(2/ε²) ∫_0^∞ r F(r) w(r) e^{−r²/ε²} dr| ≤ C K_A (2/ε²) e^{−1/(8ε)}` with
`K_A = ∫_0^∞ (A + r² + r) e^{−r²/2} dr`; and `(2/ε²) e^{−1/(8ε)} → 0` (`tendsto_polarTailFac`).
Elementary bounds (`log x ≤ x`, `r² ≥ ε/4`), following the paper's sketch.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace LQGMetric.DFGPS

/-- the dominating Gaussian weight `(A + r² + r) e^{−r²/2}` -/
def tailW (A r : ℝ) : ℝ := (A + r ^ 2 + r) * Real.exp (-(1 / 2) * r ^ 2)

lemma integrableOn_tailW (A : ℝ) : IntegrableOn (tailW A) (Ioi 0) := by
  have hb : (0 : ℝ) < 1 / 2 := by norm_num
  have h0 := (integrable_exp_neg_mul_sq hb).integrableOn (s := Ioi (0 : ℝ))
  have h1 := (integrable_mul_exp_neg_mul_sq hb).integrableOn (s := Ioi (0 : ℝ))
  have h2 : IntegrableOn (fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-(1 / 2) * x ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq hb (by norm_num)
  simp_rw [Real.rpow_two] at h2
  have := ((h0.const_mul A).add h2).add h1
  refine IntegrableOn.congr_fun this (fun r _ => ?_) measurableSet_Ioi
  simp only [tailW, Pi.add_apply]; ring

/-- `K_A` -/
def tailK (A : ℝ) : ℝ := ∫ r in Ioi 0, tailW A r

lemma max_log_le {A r : ℝ} (hA : 0 ≤ A) (hr : 0 < r) :
    max (max (A * Real.log (1 / r)) (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 ≤ A / r + r + 1 := by
  have h1 : Real.log (1 / r) ≤ 1 / r := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 / r by positivity); linarith
  have h2 : Real.log r ≤ r := by have := Real.log_le_sub_one_of_pos hr; linarith
  have hAr : 0 ≤ A / r := by positivity
  rw [show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one]
  refine max_le (max_le ?_ ?_) ?_
  · calc A * Real.log (1 / r) ≤ A * (1 / r) := mul_le_mul_of_nonneg_left h1 hA
      _ = A / r := by ring
      _ ≤ _ := by linarith
  · linarith
  · linarith

lemma exp_tail_le {ε r : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hr : Real.sqrt ε / 2 < r) :
    Real.exp (-r ^ 2 / ε ^ 2) ≤ Real.exp (-(1 / (8 * ε))) * Real.exp (-(1 / 2) * r ^ 2) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have ht : ε / 4 ≤ r ^ 2 := by
    have h0 : 0 ≤ Real.sqrt ε / 2 := by positivity
    have := pow_le_pow_left₀ h0 hr.le 2
    rw [div_pow, Real.sq_sqrt hε.le] at this
    linarith
  have e : -r ^ 2 / ε ^ 2 = -(r ^ 2 / (2 * ε ^ 2)) - r ^ 2 / (2 * ε ^ 2) := by
    field_simp; ring
  have h1 : 1 / (8 * ε) ≤ r ^ 2 / (2 * ε ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h2 : r ^ 2 / 2 ≤ r ^ 2 / (2 * ε ^ 2) := by
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith
  rw [e]; linarith

/-- **The tail estimate** (DFGPS T:726–733). -/
theorem abs_polar_tail_le {A C ε : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {F w : ℝ → ℝ}
    (hF : ∀ r : ℝ, 0 < r →
      |F r| ≤ C * max (max (A * Real.log (1 / r)) (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1)
    (hw0 : ∀ r, 0 ≤ w r) (hw1 : ∀ r, w r ≤ 1) (hwz : ∀ r, 0 < r → r ≤ Real.sqrt ε / 2 → w r = 0) :
    |2 / ε ^ 2 * ∫ r in Ioi 0, r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2)| ≤
      C * tailK A * (2 / ε ^ 2 * Real.exp (-(1 / (8 * ε)))) := by
  have ig : Integrable (fun r => C * Real.exp (-(1 / (8 * ε))) * tailW A r)
      (volume.restrict (Ioi 0)) := (integrableOn_tailW A).const_mul _
  have key := norm_integral_le_of_norm_le (f := fun r => r * F r * w r *
      Real.exp (-r ^ 2 / ε ^ 2)) ig ?_
  · rw [integral_const_mul, Real.norm_eq_abs] at key
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 / ε ^ 2)]
    calc 2 / ε ^ 2 * |∫ r in Ioi 0, r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2)|
        ≤ 2 / ε ^ 2 * (C * Real.exp (-(1 / (8 * ε))) * tailK A) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = _ := by unfold tailK; ring
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
  have hr : 0 < r := hr
  have hW : 0 ≤ tailW A r := by unfold tailW; positivity
  by_cases hrs : r ≤ Real.sqrt ε / 2
  · rw [hwz r hr hrs]; simp only [mul_zero, zero_mul, norm_zero]; positivity
  push Not at hrs
  have he := exp_tail_le hε hε1 hrs
  have hFr := (hF r hr).trans (mul_le_mul_of_nonneg_left (max_log_le hA hr) hC)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos hr, abs_of_nonneg (hw0 r),
    abs_of_pos (Real.exp_pos _)]
  calc r * |F r| * w r * Real.exp (-r ^ 2 / ε ^ 2)
      ≤ r * (C * (A / r + r + 1)) * 1 *
          (Real.exp (-(1 / (8 * ε))) * Real.exp (-(1 / 2) * r ^ 2)) := by
        gcongr
        all_goals first | exact hw1 r | exact hw0 r
    _ = C * Real.exp (-(1 / (8 * ε))) * tailW A r := by
        unfold tailW; field_simp

/-- `(2/ε²) e^{−1/(8ε)} → 0` as `ε → 0⁺`. -/
theorem tendsto_polarTailFac :
    Tendsto (fun ε : ℝ => 2 / ε ^ 2 * Real.exp (-(1 / (8 * ε)))) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun ε : ℝ => 1 / (8 * ε)) (𝓝[>] 0) atTop := by
    have : Tendsto (fun ε : ℝ => 8 * ε) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun ε : ℝ => 8 * ε) (𝓝 0) (𝓝 (8 * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        exact mul_pos (by norm_num : (0 : ℝ) < 8) hε
    refine (tendsto_inv_nhdsGT_zero.comp this).congr fun ε => ?_
    simp [one_div]
  have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp h1
  have h3 := h2.const_mul 128
  rw [mul_zero] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε : 0 < ε := hε
  simp only [Function.comp_apply]
  field_simp
  ring

end LQGMetric.DFGPS
