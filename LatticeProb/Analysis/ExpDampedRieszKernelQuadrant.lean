/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# An exponentially damped Riesz kernel on the quadrant `[0, ∞)²`

For `c > 0` and `0 < θ ≤ 1`, the kernel `exp (-c max (u, v)) |u - v| ^ (θ - 1)` is integrable for Lebesgue
measure on `[0, ∞)²`. Such kernels bound the two-time correlations `P(‖B_u - B_v‖ < a, u, v < τ)` of a planar
Brownian motion `B` killed at an exit time `τ` with an exponential tail.

* `intervalIntegrable_abs_rpow`: `|x| ^ s` is interval integrable on every interval for `s > -1`.
* `lintegral_exp_neg_max_mul_abs_sub_rpow_lt_top`: the finiteness of
  `∫∫_{[0, ∞)²} exp (-c max (u, v)) |u - v| ^ (θ - 1) du dv`.

The proof splits `|u - v| ^ (θ - 1) ≤ 1_{|u - v| ≤ 1} |u - v| ^ (θ - 1) + 1`, bounds `exp (-c max (u, v))` by
`exp (-c u)` on the first term (translation invariance in `v`) and by `exp (-c u / 2) exp (-c v / 2)` on the
second term (a product integral).
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb.Analysis

/-- The function `|x| ^ s` is interval integrable on every interval `[a, b]` when `s > -1`. -/
theorem intervalIntegrable_abs_rpow {s : ℝ} (hs : -1 < s) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => |x| ^ s) volume a b := by
  have h0 : ∀ c : ℝ, 0 ≤ c → IntervalIntegrable (fun x : ℝ => |x| ^ s) volume 0 c := by
    intro c hc
    have h := intervalIntegral.intervalIntegrable_rpow' hs (a := 0) (b := c)
    rw [intervalIntegrable_iff, uIoc_of_le hc] at h ⊢
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioc
    simp only [abs_of_pos hx.1]
  have h1 : ∀ c : ℝ, IntervalIntegrable (fun x : ℝ => |x| ^ s) volume 0 c := by
    intro c
    rcases le_total 0 c with hc | hc
    · exact h0 c hc
    · rw [IntervalIntegrable.iff_comp_neg]
      simpa only [abs_neg, neg_zero] using h0 (-c) (by linarith)
  exact (h1 a).symm.trans (h1 b)

/-- **Exponentially damped Riesz kernel on the quadrant.** For `c > 0` and `0 < θ ≤ 1`,
`∫∫_{[0, ∞)²} exp (-c max (u, v)) |u - v| ^ (θ - 1) du dv < ∞`, the measure being the product of Lebesgue
measure on `[0, ∞)` with itself. -/
theorem lintegral_exp_neg_max_mul_abs_sub_rpow_lt_top {c θ : ℝ} (hc : 0 < c) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) :
    ∫⁻ p, ENNReal.ofReal (Real.exp (-c * max p.1 p.2) * |p.1 - p.2| ^ (θ - 1))
      ∂((volume.restrict (Ici (0 : ℝ))).prod (volume.restrict (Ici (0 : ℝ)))) < ∞ := by
  set μ : Measure ℝ := volume.restrict (Ici (0 : ℝ))
  -- the local singularity, cut off at distance one
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = (Icc (-1 : ℝ) 1).indicator (fun w => |w| ^ (θ - 1)) := ⟨_, rfl⟩
  have hgm : Measurable g := by
    rw [hg]
    exact (continuous_abs.measurable.pow_const _).indicator measurableSet_Icc
  have hgi : Integrable g volume := by
    rw [hg, integrable_indicator_iff measurableSet_Icc]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).1
      (intervalIntegrable_abs_rpow (by linarith) (-1) 1)
  have hg0 : ∀ w, 0 ≤ g w := by
    rw [hg]
    exact fun w => Set.indicator_nonneg (fun x _ => Real.rpow_nonneg (abs_nonneg x) _) w
  -- exponential weights on the half-line
  have hexp : ∀ b : ℝ, 0 < b → ∫⁻ x, ENNReal.ofReal (Real.exp (-b * x)) ∂μ < ∞ := by
    intro b hb
    have h : IntegrableOn (fun x => Real.exp (-b * x)) (Ici (0 : ℝ)) volume :=
      (integrableOn_Ici_iff_integrableOn_Ioi).2 (exp_neg_integrableOn_Ioi 0 hb)
    exact h.setLIntegral_lt_top
  -- pointwise domination
  have hpt : ∀ p : ℝ × ℝ, ENNReal.ofReal (Real.exp (-c * max p.1 p.2) * |p.1 - p.2| ^ (θ - 1)) ≤
      ENNReal.ofReal (Real.exp (-c * p.1)) * ENNReal.ofReal (g (p.2 - p.1)) +
      ENNReal.ofReal (Real.exp (-(c / 2) * p.1)) * ENNReal.ofReal (Real.exp (-(c / 2) * p.2)) := by
    intro p
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le (hg0 _))
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hE : 0 ≤ Real.exp (-c * max p.1 p.2) := (Real.exp_pos _).le
    have hR : 0 ≤ |p.1 - p.2| ^ (θ - 1) := Real.rpow_nonneg (abs_nonneg _) _
    have hB : 0 ≤ Real.exp (-(c / 2) * p.1) * Real.exp (-(c / 2) * p.2) := by positivity
    have hA : 0 ≤ Real.exp (-c * p.1) * g (p.2 - p.1) := mul_nonneg (Real.exp_pos _).le (hg0 _)
    by_cases hw : |p.2 - p.1| ≤ 1
    · have hmem : p.2 - p.1 ∈ Icc (-1 : ℝ) 1 := abs_le.1 hw
      have hgw : g (p.2 - p.1) = |p.1 - p.2| ^ (θ - 1) := by
        rw [hg, Set.indicator_of_mem hmem, abs_sub_comm]
      have h1 : Real.exp (-c * max p.1 p.2) ≤ Real.exp (-c * p.1) :=
        Real.exp_le_exp.2 (by nlinarith [le_max_left p.1 p.2])
      rw [hgw]
      nlinarith
    · have hr : |p.1 - p.2| ^ (θ - 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by rw [abs_sub_comm]; exact (not_le.1 hw).le)
          (by linarith)
      have h1 : Real.exp (-c * max p.1 p.2) ≤
          Real.exp (-(c / 2) * p.1) * Real.exp (-(c / 2) * p.2) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.2 (by nlinarith [le_max_left p.1 p.2, le_max_right p.1 p.2])
      nlinarith
  have hAm : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (-c * p.1)) * ENNReal.ofReal (g (p.2 - p.1)) := by
    have h2 : Measurable fun p : ℝ × ℝ => g (p.2 - p.1) := hgm.comp (measurable_snd.sub measurable_fst)
    exact (Real.measurable_exp.comp (measurable_fst.const_mul (-c))).ennreal_ofReal.mul
      h2.ennreal_ofReal
  -- the singular part: translation invariance in the second variable
  have hAfin : ∫⁻ p, ENNReal.ofReal (Real.exp (-c * p.1)) * ENNReal.ofReal (g (p.2 - p.1))
      ∂(μ.prod μ) < ∞ := by
    rw [lintegral_prod _ hAm.aemeasurable]
    have hinner : ∀ u : ℝ, ∫⁻ v, ENNReal.ofReal (Real.exp (-c * (u, v).1)) *
        ENNReal.ofReal (g ((u, v).2 - (u, v).1)) ∂μ ≤
        ENNReal.ofReal (Real.exp (-c * u)) * ∫⁻ w, ENNReal.ofReal (g w) := by
      intro u
      dsimp only
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr _ * ?_
      calc ∫⁻ v, ENNReal.ofReal (g (v - u)) ∂μ ≤ ∫⁻ v, ENNReal.ofReal (g (v - u)) :=
            lintegral_mono' Measure.restrict_le_self le_rfl
        _ = ∫⁻ w, ENNReal.ofReal (g w) := lintegral_sub_right_eq_self (fun w => ENNReal.ofReal (g w)) u
    refine lt_of_le_of_lt (lintegral_mono hinner) ?_
    rw [lintegral_mul_const' _ _ hgi.lintegral_lt_top.ne]
    exact ENNReal.mul_lt_top (hexp c hc) hgi.lintegral_lt_top
  -- the regular part: a product integral
  have hBfin : ∫⁻ p, ENNReal.ofReal (Real.exp (-(c / 2) * p.1)) *
      ENNReal.ofReal (Real.exp (-(c / 2) * p.2)) ∂(μ.prod μ) < ∞ := by
    have hm : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-(c / 2) * x)) :=
      (Real.measurable_exp.comp (measurable_id.const_mul _)).ennreal_ofReal
    have h := lintegral_prod_mul (μ := μ) (ν := μ)
      (f := fun x => ENNReal.ofReal (Real.exp (-(c / 2) * x)))
      (g := fun x => ENNReal.ofReal (Real.exp (-(c / 2) * x))) hm.aemeasurable hm.aemeasurable
    refine h.trans_lt ?_
    exact ENNReal.mul_lt_top (hexp _ (by linarith)) (hexp _ (by linarith))
  calc ∫⁻ p, ENNReal.ofReal (Real.exp (-c * max p.1 p.2) * |p.1 - p.2| ^ (θ - 1)) ∂(μ.prod μ)
      ≤ ∫⁻ p, (ENNReal.ofReal (Real.exp (-c * p.1)) * ENNReal.ofReal (g (p.2 - p.1)) +
          ENNReal.ofReal (Real.exp (-(c / 2) * p.1)) * ENNReal.ofReal (Real.exp (-(c / 2) * p.2)))
          ∂(μ.prod μ) := lintegral_mono hpt
    _ = (∫⁻ p, ENNReal.ofReal (Real.exp (-c * p.1)) * ENNReal.ofReal (g (p.2 - p.1)) ∂(μ.prod μ)) +
          ∫⁻ p, ENNReal.ofReal (Real.exp (-(c / 2) * p.1)) *
            ENNReal.ofReal (Real.exp (-(c / 2) * p.2)) ∂(μ.prod μ) := lintegral_add_left hAm _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hAfin, hBfin⟩

end LatticeProb.Analysis
