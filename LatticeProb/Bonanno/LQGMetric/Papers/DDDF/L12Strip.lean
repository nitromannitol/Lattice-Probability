/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L12Strip at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DDDF Lemma 12′, node S12a: the strip map `G(ζ) = log((1+ζ)/(1−ζ))`

Decision D-B4 (`decisions/DEC-B.md` §(d)) replaces the Riemann maps between ellipses of
DDDF Lemma 12 (Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `tightness.tex` l. 744–760) =
DF Thm 3.1 Step 1 (Dubédat–Falconet, arXiv:1809.02607, `LiouvilleMetricStarScale.tex` l. 640–660)
by explicit maps built from `G(ζ) = log((1+ζ)/(1−ζ))` (`sG`), which maps the unit disc onto the
strip `|Im w| < π/2`, with inverse `T(w) = (e^w − 1)/(e^w + 1) = tanh(w/2)` (`sT`).

This file: `sG ∘ sT = id` on the strip, `sT ∘ sG = id` on the disc, `|Im G| < π/2`,
holomorphy, the real-part bounds of `G` near `±ρ`, and the explicit real/imaginary parts and
modulus of `T(u + iv)` (from which `|T(u+iv)| ≤ ρ ⇔ cos v ≥ k cosh u`, `k = (1−ρ²)/(1+ρ²)`).
All are own elementary computations (standard facts about `artanh`), recorded under D-DDDF-14.
-/

namespace LQGMetric.DDDF.L12

open Set Real

/-- The strip map `G(ζ) = log((1+ζ)/(1−ζ)) = 2 artanh ζ`. -/
noncomputable def sG (ζ : ℂ) : ℂ := Complex.log ((1 + ζ) / (1 - ζ))

/-- Its inverse `T(w) = (e^w − 1)/(e^w + 1) = tanh(w/2)`. -/
noncomputable def sT (w : ℂ) : ℂ := (Complex.exp w - 1) / (Complex.exp w + 1)

lemma one_sub_ne_zero' {ζ : ℂ} (h : ‖ζ‖ < 1) : 1 - ζ ≠ 0 := by
  intro h0
  have : ζ = 1 := by linear_combination -h0
  simp [this] at h

lemma one_add_ne_zero' {ζ : ℂ} (h : ‖ζ‖ < 1) : 1 + ζ ≠ 0 := by
  intro h0
  have : ζ = -1 := by linear_combination h0
  simp [this] at h

lemma re_quot_pos {ζ : ℂ} (h : ‖ζ‖ < 1) : 0 < ((1 + ζ) / (1 - ζ)).re := by
  have hn : 0 < Complex.normSq (1 - ζ) := Complex.normSq_pos.2 (one_sub_ne_zero' h)
  have h2 : ζ.re * ζ.re + ζ.im * ζ.im < 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg ζ]
  rw [Complex.div_re]
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
    Complex.sub_im]
  rw [← add_div]; apply div_pos _ hn; nlinarith

lemma quot_mem_slitPlane {ζ : ℂ} (h : ‖ζ‖ < 1) : (1 + ζ) / (1 - ζ) ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inl (re_quot_pos h))

lemma cos_pos_of_abs_lt {v : ℝ} (hv : |v| < π / 2) : 0 < Real.cos v :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le v], by linarith [le_abs_self v]⟩

lemma exp_add_one_ne {w : ℂ} (hw : |w.im| < π / 2) : Complex.exp w + 1 ≠ 0 := by
  intro h
  have h1 : 0 < (Complex.exp w + 1).re := by
    have := cos_pos_of_abs_lt hw
    simp only [Complex.add_re, Complex.exp_re, Complex.one_re]; positivity
  rw [h] at h1; simp at h1

/-- `G ∘ T = id` on the strip `|Im w| < π/2`. -/
theorem sG_sT {w : ℂ} (hw : |w.im| < π / 2) : sG (sT w) = w := by
  have hne := exp_add_one_ne hw
  have h1 : 1 + sT w = 2 * Complex.exp w / (Complex.exp w + 1) := by
    unfold sT; field_simp; ring
  have h2 : 1 - sT w = 2 / (Complex.exp w + 1) := by
    unfold sT; field_simp; ring
  have h : (1 + sT w) / (1 - sT w) = Complex.exp w := by
    rw [h1, h2]; field_simp
  rw [sG, h, Complex.log_exp] <;>
    [linarith [neg_abs_le w.im, Real.pi_pos]; linarith [le_abs_self w.im, Real.pi_pos]]

/-- `T ∘ G = id` on the unit disc. -/
theorem sT_sG {ζ : ℂ} (hζ : ‖ζ‖ < 1) : sT (sG ζ) = ζ := by
  have ha := one_add_ne_zero' hζ
  have hs := one_sub_ne_zero' hζ
  have he : Complex.exp (sG ζ) = (1 + ζ) / (1 - ζ) :=
    Complex.exp_log (div_ne_zero ha hs)
  have h1 : (1 + ζ) / (1 - ζ) - 1 = 2 * ζ / (1 - ζ) := by field_simp; ring
  have h2 : (1 + ζ) / (1 - ζ) + 1 = 2 / (1 - ζ) := by field_simp; ring
  rw [sT, he, h1, h2]; field_simp

/-- `G` maps the disc into the strip `|Im w| < π/2`. -/
theorem abs_im_sG_lt {ζ : ℂ} (hζ : ‖ζ‖ < 1) : |(sG ζ).im| < π / 2 := by
  rw [sG, Complex.log_im]
  exact Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (re_quot_pos hζ))

theorem differentiableAt_sG {ζ : ℂ} (hζ : ‖ζ‖ < 1) : DifferentiableAt ℂ sG ζ := by
  have : DifferentiableAt ℂ (fun ζ : ℂ => (1 + ζ) / (1 - ζ)) ζ :=
    ((differentiableAt_const _).add differentiableAt_id).div
      ((differentiableAt_const _).sub differentiableAt_id) (one_sub_ne_zero' hζ)
  exact this.clog (quot_mem_slitPlane hζ)

theorem differentiableAt_sT {w : ℂ} (hw : |w.im| < π / 2) : DifferentiableAt ℂ sT w :=
  (Complex.differentiableAt_exp.sub_const 1).div (Complex.differentiableAt_exp.add_const 1)
    (exp_add_one_ne hw)

theorem injOn_sG : InjOn sG (Metric.ball 0 1) := by
  intro x hx y hy hxy
  rw [Metric.mem_ball, dist_zero_right] at hx hy
  rw [← sT_sG hx, ← sT_sG hy, hxy]

theorem injOn_sT : InjOn sT {w : ℂ | |w.im| < π / 2} := by
  intro x hx y hy hxy
  rw [← sG_sT hx, ← sG_sT hy, hxy]

/-- Near `−ρ`, the real part of `G` is very negative. -/
theorem re_sG_le {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {ξ : ℂ} (hξ1 : ‖ξ‖ < 1)
    (hξ : ‖ξ + ρ‖ ≤ 1 - ρ) : (sG ξ).re ≤ Real.log ((1 - ρ) / ρ) := by
  have e1 : (1 : ℂ) + ξ = ((1 - ρ : ℝ) : ℂ) + (ξ + ρ) := by push_cast; ring
  have n1 : ‖1 + ξ‖ ≤ 2 * (1 - ρ) := by
    rw [e1]
    calc _ ≤ ‖((1 - ρ : ℝ) : ℂ)‖ + ‖ξ + ρ‖ := norm_add_le _ _
      _ ≤ _ := by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
  have e2 : (1 : ℂ) - ξ = ((1 + ρ : ℝ) : ℂ) - (ξ + ρ) := by push_cast; ring
  have n2 : 2 * ρ ≤ ‖1 - ξ‖ := by
    rw [e2]
    have := norm_sub_norm_le (((1 + ρ : ℝ)) : ℂ) (ξ + ρ)
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)] at this; linarith
  have hp1 := norm_pos_iff.2 (one_add_ne_zero' hξ1)
  rw [sG, Complex.log_re, norm_div]
  apply Real.log_le_log (div_pos hp1 (by linarith))
  rw [div_le_div_iff₀ (by linarith) hρ0]; nlinarith

/-- Near `ρ`, the real part of `G` is very positive. -/
theorem le_re_sG {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {ξ : ℂ} (hξ1 : ‖ξ‖ < 1)
    (hξ : ‖ξ - ρ‖ ≤ 1 - ρ) : Real.log (ρ / (1 - ρ)) ≤ (sG ξ).re := by
  have e1 : (1 : ℂ) - ξ = ((1 - ρ : ℝ) : ℂ) - (ξ - ρ) := by push_cast; ring
  have n1 : ‖1 - ξ‖ ≤ 2 * (1 - ρ) := by
    rw [e1]
    calc _ ≤ ‖((1 - ρ : ℝ) : ℂ)‖ + ‖ξ - ρ‖ := norm_sub_le _ _
      _ ≤ _ := by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
  have e2 : (1 : ℂ) + ξ = ((1 + ρ : ℝ) : ℂ) + (ξ - ρ) := by push_cast; ring
  have n2 : 2 * ρ ≤ ‖1 + ξ‖ := by
    rw [e2]
    have := norm_sub_norm_le (((1 + ρ : ℝ)) : ℂ) (-(ξ - ρ))
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith), norm_neg, sub_neg_eq_add] at this
    linarith
  have hp1 := norm_pos_iff.2 (one_sub_ne_zero' hξ1)
  rw [sG, Complex.log_re, norm_div]
  apply Real.log_le_log (div_pos hρ0 (by linarith))
  rw [div_le_div_iff₀ (by linarith) hp1]; nlinarith

/-- Real part, imaginary part and squared modulus of `T(u + iv)`, `E = e^u`. -/
theorem sT_parts (w : ℂ) (hw : |w.im| < π / 2) :
    (sT w).re = (Real.exp w.re ^ 2 - 1) /
        (Real.exp w.re ^ 2 + 2 * Real.exp w.re * Real.cos w.im + 1) ∧
      (sT w).im = 2 * Real.exp w.re * Real.sin w.im /
        (Real.exp w.re ^ 2 + 2 * Real.exp w.re * Real.cos w.im + 1) ∧
      Complex.normSq (sT w) = (Real.exp w.re ^ 2 - 2 * Real.exp w.re * Real.cos w.im + 1) /
        (Real.exp w.re ^ 2 + 2 * Real.exp w.re * Real.cos w.im + 1) := by
  set E := Real.exp w.re
  set c := Real.cos w.im
  set s := Real.sin w.im
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hc := cos_pos_of_abs_lt hw
  have hE : 0 < E := Real.exp_pos _
  have hD : 0 < E ^ 2 + 2 * E * c + 1 := by positivity
  have hden : (E * c + 1) * (E * c + 1) + E * s * (E * s) = E ^ 2 + 2 * E * c + 1 := by
    linear_combination E ^ 2 * hsc
  have hnum : (E * c - 1) * (E * c - 1) + E * s * (E * s) = E ^ 2 - 2 * E * c + 1 := by
    linear_combination E ^ 2 * hsc
  have hre : (sT w).re = (E ^ 2 - 1) / (E ^ 2 + 2 * E * c + 1) := by
    unfold sT
    simp only [Complex.div_re, Complex.normSq_apply, Complex.sub_re, Complex.add_re,
      Complex.exp_re, Complex.exp_im, Complex.one_re, Complex.sub_im, Complex.add_im,
      Complex.one_im, sub_zero, add_zero]
    rw [hden, ← add_div]; congr 1; linear_combination E ^ 2 * hsc
  have him : (sT w).im = 2 * E * s / (E ^ 2 + 2 * E * c + 1) := by
    unfold sT
    simp only [Complex.div_im, Complex.normSq_apply, Complex.sub_re, Complex.add_re,
      Complex.exp_re, Complex.exp_im, Complex.one_re, Complex.sub_im, Complex.add_im,
      Complex.one_im, sub_zero, add_zero]
    rw [hden, ← sub_div]; congr 1; ring
  refine ⟨hre, him, ?_⟩
  rw [Complex.normSq_apply, hre, him]
  rw [div_mul_div_comm, div_mul_div_comm, ← add_div, div_eq_div_iff (by positivity) hD.ne']
  linear_combination (4 * E ^ 2 * (E ^ 2 + 2 * E * c + 1)) * hsc

end LQGMetric.DDDF.L12
