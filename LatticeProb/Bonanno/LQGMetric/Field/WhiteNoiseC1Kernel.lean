/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoiseC1Kernel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseKernel
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Pointwise analysis of the heat kernel for the `C¹` version of `φ_{a,b}` (task P2-DDDFFIELD)

DDDF (arXiv:1904.08021, `tightness.tex` l. 292: "a.s. smooth version"; l. 325–345 use `∇φ_{0,n}`)
needs a `C¹` version of `φ_{a,b}(x) = √π ∫∫ 1_{[a²,b²]}(t) p_{t/2}(x − y) W(dy, dt)`. The
derivative falls on the kernel: `∂_e p_s(v) = −(⟪e, v⟫/s) p_s(v)`. This file has the elementary
facts on the Gaussian `g_s(v) = (2πs)⁻¹ e^{−|v|²/(2s)}` (so `p_s(x, y) = g_s(x − y)`):

* `hasFDerivAt_gk`, `hasFDerivAt_gkD`: the first two derivatives;
* `abs_gkD_le`, `norm_gkDD_le`: `|∂_e g_s|, ‖D ∂_e g_s‖ ≤ (5 + 4s)/(2πs²) e^{−|v|²/(4s)}`
  (`X e^{−X/c} ≤ 2c e^{−X/(2c)}`);
* `gk_add_smul_sub`: `g_s(v + h e) − g_s(v) = h ∫₀¹ ∂_e g_s(v + r h e) dr` (FTC);
* `abs_dq_sub_le`, `abs_dq_le`: the difference quotient `dq` is bounded and Lipschitz in
  `(x, h)` with a Gaussian-decaying constant (mean value theorem).

All of this is an own elementary proof (standard calculus of the Gaussian; DDDF give no proof
of the smoothness of `φ_{a,b}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace

namespace LQGMetric
namespace WhiteNoise

/-- The Gaussian `g_s(v) = (2πs)⁻¹ e^{−|v|²/(2s)}`; `p_s(x, y) = g_s(x − y)`. -/
def gk (s : ℝ) (v : ℂ) : ℝ := (2 * Real.pi * s)⁻¹ * Real.exp (-‖v‖ ^ 2 / (2 * s))

lemma heatKernel_eq_gk (s : ℝ) (x y : ℂ) : heatKernel s x y = gk s (x - y) := rfl

lemma continuous_gk (s : ℝ) : Continuous (gk s) := by unfold gk; fun_prop

lemma gk_nonneg {s : ℝ} (hs : 0 ≤ s) (v : ℂ) : 0 ≤ gk s v := by unfold gk; positivity

/-- The directional derivative `∂_e g_s(v) = −(⟪e, v⟫/s) g_s(v)`. -/
def gkD (s : ℝ) (e v : ℂ) : ℝ := -(⟪e, v⟫ / s) * gk s v

lemma continuous_gkD (s : ℝ) (e : ℂ) : Continuous (gkD s e) := by
  unfold gkD
  exact ((continuous_const.inner continuous_id).div_const s).neg.mul (continuous_gk s)

lemma hasFDerivAt_gk {s : ℝ} (hs : s ≠ 0) (v : ℂ) :
    HasFDerivAt (gk s) (-(gk s v / s) • innerSL ℝ v) v := by
  have e1 : (fun w : ℂ => -‖w‖ ^ 2 / (2 * s)) = fun w => (-(2 * s)⁻¹) * ‖w‖ ^ 2 := by
    funext w; ring
  have h1 : HasFDerivAt (fun w : ℂ => -‖w‖ ^ 2 / (2 * s))
      ((-(2 * s)⁻¹) • (2 • innerSL ℝ v)) v := by
    rw [e1]; exact (hasStrictFDerivAt_norm_sq v).hasFDerivAt.const_mul _
  have h2 := h1.exp.const_mul ((2 * Real.pi * s)⁻¹)
  refine h2.congr_fderiv ?_
  refine ContinuousLinearMap.ext (fun w : ℂ => ?_)
  simp only [gk, ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat]
  field_simp

/-- The derivative of `∂_e g_s`. -/
def gkDD (s : ℝ) (e v : ℂ) : ℂ →L[ℝ] ℝ :=
  (-s⁻¹) • (⟪e, v⟫ • (-(gk s v / s) • innerSL ℝ v) + gk s v • innerSL ℝ e)

lemma hasFDerivAt_gkD {s : ℝ} (hs : s ≠ 0) (e v : ℂ) :
    HasFDerivAt (gkD s e) (gkDD s e v) v := by
  have e1 : gkD s e = fun w => (-s⁻¹) * (⟪e, w⟫ * gk s w) := by
    funext w; simp only [gkD]; ring
  rw [e1]
  exact (((innerSL ℝ e).hasFDerivAt).mul (hasFDerivAt_gk hs v)).const_mul _

/-- `X e^{−X/c} ≤ 2c e^{−X/(2c)}` (from `y ≤ e^y`). -/
lemma mul_exp_neg_div_le {X c : ℝ} (hX : 0 ≤ X) (hc : 0 < c) :
    X * Real.exp (-X / c) ≤ 2 * c * Real.exp (-X / (2 * c)) := by
  have h1 : X / (2 * c) ≤ Real.exp (X / (2 * c)) := by
    have := Real.add_one_le_exp (X / (2 * c)); linarith
  have h2 : X ≤ 2 * c * Real.exp (X / (2 * c)) := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * c)).1 h1; linarith
  have hAB : Real.exp (X / (2 * c)) * Real.exp (-X / (2 * c)) = 1 := by
    rw [← Real.exp_add, neg_div, add_neg_cancel, Real.exp_zero]
  have e : Real.exp (-X / c) = Real.exp (-X / (2 * c)) * Real.exp (-X / (2 * c)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [e]
  have hB := (Real.exp_pos (-X / (2 * c))).le
  calc X * (Real.exp (-X / (2 * c)) * Real.exp (-X / (2 * c)))
      ≤ (2 * c * Real.exp (X / (2 * c))) * (Real.exp (-X / (2 * c)) *
          Real.exp (-X / (2 * c))) := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = 2 * c * Real.exp (-X / (2 * c)) := by
        rw [show 2 * c * Real.exp (X / (2 * c)) * (Real.exp (-X / (2 * c)) *
          Real.exp (-X / (2 * c))) = 2 * c * (Real.exp (X / (2 * c)) *
          Real.exp (-X / (2 * c))) * Real.exp (-X / (2 * c)) by ring, hAB, mul_one]

/-- The common bound `B_s = (5 + 4s)/(2πs²)`. -/
def gkB (s : ℝ) : ℝ := (5 + 4 * s) / (2 * Real.pi * s ^ 2)

lemma gk_bounds {s : ℝ} (hs : 0 < s) (v : ℂ) :
    Real.exp (-‖v‖ ^ 2 / (2 * s)) ≤ Real.exp (-‖v‖ ^ 2 / (4 * s)) ∧
      ‖v‖ ^ 2 * Real.exp (-‖v‖ ^ 2 / (2 * s)) ≤ 4 * s * Real.exp (-‖v‖ ^ 2 / (4 * s)) := by
  constructor
  · rw [Real.exp_le_exp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ‖v‖]
  · have := mul_exp_neg_div_le (sq_nonneg ‖v‖) (by positivity : (0 : ℝ) < 2 * s)
    convert this using 2 <;> ring_nf

lemma abs_gkD_le {s : ℝ} (hs : 0 < s) {e : ℂ} (he : ‖e‖ ≤ 1) (v : ℂ) :
    |gkD s e v| ≤ gkB s * Real.exp (-‖v‖ ^ 2 / (4 * s)) := by
  obtain ⟨h1, h2⟩ := gk_bounds hs v
  set E := Real.exp (-‖v‖ ^ 2 / (2 * s))
  set E4 := Real.exp (-‖v‖ ^ 2 / (4 * s))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hin : |⟪e, v⟫| ≤ 1 + ‖v‖ ^ 2 := by
    refine (abs_real_inner_le_norm e v).trans ?_
    nlinarith [norm_nonneg v, norm_nonneg e, sq_nonneg (‖v‖ - 1)]
  have hpi := Real.pi_pos
  have hg : gk s v = (2 * Real.pi * s)⁻¹ * E := rfl
  rw [gkD, abs_mul, abs_neg, abs_div, abs_of_pos hs, abs_of_nonneg (gk_nonneg hs.le v), hg]
  calc |⟪e, v⟫| / s * ((2 * Real.pi * s)⁻¹ * E)
      ≤ (1 + ‖v‖ ^ 2) / s * ((2 * Real.pi * s)⁻¹ * E) := by gcongr
    _ = (E + ‖v‖ ^ 2 * E) / (2 * Real.pi * s ^ 2) := by field_simp
    _ ≤ (E4 + 4 * s * E4) / (2 * Real.pi * s ^ 2) := by gcongr <;> linarith
    _ ≤ gkB s * E4 := by
        rw [gkB, div_mul_eq_mul_div]
        gcongr
        nlinarith [(Real.exp_pos (-‖v‖ ^ 2 / (4 * s))).le]

lemma norm_gkDD_le {s : ℝ} (hs : 0 < s) {e : ℂ} (he : ‖e‖ ≤ 1) (v : ℂ) :
    ‖gkDD s e v‖ ≤ gkB s * Real.exp (-‖v‖ ^ 2 / (4 * s)) := by
  obtain ⟨h1, h2⟩ := gk_bounds hs v
  set E := Real.exp (-‖v‖ ^ 2 / (2 * s))
  set E4 := Real.exp (-‖v‖ ^ 2 / (4 * s))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hE4 : 0 ≤ E4 := (Real.exp_pos _).le
  have hpi := Real.pi_pos
  have hg : gk s v = (2 * Real.pi * s)⁻¹ * E := rfl
  have hg0 : 0 ≤ gk s v := by rw [hg]; positivity
  have hb : ‖gkDD s e v‖ ≤ s⁻¹ * (‖v‖ * (gk s v / s * ‖v‖) + gk s v * 1) := by
    unfold gkDD
    rw [norm_smul, norm_neg, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
    gcongr
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, norm_smul, norm_neg, innerSL_apply_norm, Real.norm_of_nonneg
        (div_nonneg hg0 hs.le), Real.norm_eq_abs]
      gcongr
      exact (abs_real_inner_le_norm e v).trans (by nlinarith [norm_nonneg v])
    · rw [norm_smul, innerSL_apply_norm, Real.norm_of_nonneg hg0]
      gcongr
  refine hb.trans ?_
  rw [hg]
  calc s⁻¹ * (‖v‖ * ((2 * Real.pi * s)⁻¹ * E / s * ‖v‖) + (2 * Real.pi * s)⁻¹ * E * 1)
      = (‖v‖ ^ 2 * E / s + E) / (2 * Real.pi * s ^ 2) := by field_simp
    _ ≤ (4 * E4 + E4) / (2 * Real.pi * s ^ 2) := by
        gcongr
        · rw [div_le_iff₀ hs]; linarith
    _ ≤ gkB s * E4 := by
        rw [gkB, div_mul_eq_mul_div]
        gcongr
        nlinarith

/-- **FTC**: `g_s(v + h e) − g_s(v) = h ∫₀¹ ∂_e g_s(v + r h e) dr`. -/
lemma gk_add_smul_sub {s : ℝ} (hs : s ≠ 0) (e v : ℂ) (h : ℝ) :
    gk s (v + h • e) - gk s v = h * ∫ r in (0 : ℝ)..1, gkD s e (v + (r * h) • e) := by
  have hd : ∀ r ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r : ℝ => gk s (v + (r * h) • e))
      (h * gkD s e (v + (r * h) • e)) r := by
    intro r _
    have hl : HasDerivAt (fun r : ℝ => v + (r * h) • e) (h • e) r := by
      have := ((hasDerivAt_id r).mul_const h).smul_const e
      simpa using this.const_add v
    have := (hasFDerivAt_gk hs (v + (r * h) • e)).comp_hasDerivAt r hl
    refine this.congr_deriv ?_
    simp only [gkD, ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul,
      inner_smul_right, real_inner_comm e]
    ring
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp
  · exact ((continuous_gkD s e).comp (by fun_prop)).const_mul h |>.intervalIntegrable 0 1

/-- The difference-quotient kernel at time `t`: `∫₀¹ ∂_e p_{t/2}(x − y + r h e) dr`
(`= (p_{t/2}(x + h e − y) − p_{t/2}(x − y))/h` for `h ≠ 0`, `= ∂_e p_{t/2}(x − y)` for `h = 0`). -/
def dq (t : ℝ) (e x : ℂ) (h : ℝ) (y : ℂ) : ℝ := ∫ r in (0 : ℝ)..1, gkD (t / 2) e (x - y + (r * h) • e)

lemma dq_zero (t : ℝ) (e x y : ℂ) : dq t e x 0 y = gkD (t / 2) e (x - y) := by simp [dq]

/-- Shift of the Gaussian decay: `‖v + y‖ ≤ ρ ⇒ e^{−|v|²/(4s)} ≤ e^{ρ²/(4s)} e^{−|y|²/(8s)}`. -/
lemma exp_shift_le {s : ℝ} (hs : 0 < s) {ρ : ℝ} {v y : ℂ} (hv : ‖v + y‖ ≤ ρ) :
    Real.exp (-‖v‖ ^ 2 / (4 * s)) ≤ Real.exp (ρ ^ 2 / (4 * s)) * Real.exp (-‖y‖ ^ 2 / (8 * s)) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have hy : ‖y‖ ≤ ‖v + y‖ + ‖v‖ := by
    calc ‖y‖ = ‖(v + y) - v‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  have h0 : 0 ≤ ‖v + y‖ := norm_nonneg _
  have hy2 : ‖y‖ ^ 2 ≤ 2 * ρ ^ 2 + 2 * ‖v‖ ^ 2 := by
    nlinarith [norm_nonneg y, norm_nonneg v, sq_nonneg (‖v + y‖ - ‖v‖)]
  have h3 : ‖y‖ ^ 2 / (8 * s) ≤ (2 * ρ ^ 2 + 2 * ‖v‖ ^ 2) / (8 * s) :=
    div_le_div_of_nonneg_right hy2 (by positivity)
  have e1 : (2 * ρ ^ 2 + 2 * ‖v‖ ^ 2) / (8 * s) = ρ ^ 2 / (4 * s) + ‖v‖ ^ 2 / (4 * s) := by
    field_simp; ring
  have e2 : -‖y‖ ^ 2 / (8 * s) = -(‖y‖ ^ 2 / (8 * s)) := by ring
  have e3 : -‖v‖ ^ 2 / (4 * s) = -(‖v‖ ^ 2 / (4 * s)) := by ring
  rw [e2, e3]
  linarith

/-- Pointwise bound: `‖x‖ + |h| ≤ ρ ⇒ |dq| ≤ B_s e^{ρ²/(4s)} e^{−|y|²/(8s)}`, `s = t/2`. -/
lemma abs_dq_le {t : ℝ} (ht : 0 < t) {e : ℂ} (he : ‖e‖ ≤ 1) {ρ : ℝ} {x : ℂ} {h : ℝ}
    (hxh : ‖x‖ + |h| ≤ ρ) (y : ℂ) :
    |dq t e x h y| ≤ gkB (t / 2) * Real.exp (ρ ^ 2 / (4 * (t / 2))) *
      Real.exp (-‖y‖ ^ 2 / (8 * (t / 2))) := by
  have hs : 0 < t / 2 := by positivity
  rw [dq, ← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := gkB (t / 2) *
    Real.exp (ρ ^ 2 / (4 * (t / 2))) * Real.exp (-‖y‖ ^ 2 / (8 * (t / 2))))
    fun r hr => ?_).trans (by simp)
  rw [uIoc_of_le zero_le_one] at hr
  rw [Real.norm_eq_abs, mul_assoc]
  refine (abs_gkD_le hs he _).trans (mul_le_mul_of_nonneg_left (exp_shift_le hs ?_)
    (by unfold gkB; positivity))
  have : ‖(r * h) • e‖ ≤ |h| := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hr.1]
    calc r * |h| * ‖e‖ ≤ 1 * |h| * 1 := by gcongr; exact hr.2
      _ = |h| := by ring
  calc ‖x - y + (r * h) • e + y‖ = ‖x + (r * h) • e‖ := by congr 1; abel
    _ ≤ ‖x‖ + ‖(r * h) • e‖ := norm_add_le _ _
    _ ≤ ρ := by linarith

/-- **Lipschitz bound** in `(x, h)`: for `‖x‖ + |h|, ‖x'‖ + |h'| ≤ ρ`,
`|dq(x,h) − dq(x',h')| ≤ B_s e^{ρ²/(4s)} e^{−|y|²/(8s)} (‖x − x'‖ + |h − h'|)`. -/
lemma abs_dq_sub_le {t : ℝ} (ht : 0 < t) {e : ℂ} (he : ‖e‖ ≤ 1) {ρ : ℝ} {x x' : ℂ} {h h' : ℝ}
    (hxh : ‖x‖ + |h| ≤ ρ) (hxh' : ‖x'‖ + |h'| ≤ ρ) (y : ℂ) :
    |dq t e x h y - dq t e x' h' y| ≤ gkB (t / 2) * Real.exp (ρ ^ 2 / (4 * (t / 2))) *
      Real.exp (-‖y‖ ^ 2 / (8 * (t / 2))) * (‖x - x'‖ + |h - h'|) := by
  have hs : 0 < t / 2 := by positivity
  have hcont : ∀ (x : ℂ) (h : ℝ), Continuous fun r : ℝ => gkD (t / 2) e (x - y + (r * h) • e) :=
    fun x h => (continuous_gkD _ e).comp (by fun_prop)
  rw [dq, dq, ← intervalIntegral.integral_sub ((hcont x h).intervalIntegrable 0 1)
    ((hcont x' h').intervalIntegrable 0 1), ← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := gkB (t / 2) *
    Real.exp (ρ ^ 2 / (4 * (t / 2))) * Real.exp (-‖y‖ ^ 2 / (8 * (t / 2))) *
    (‖x - x'‖ + |h - h'|)) fun r hr => ?_).trans (by simp)
  rw [uIoc_of_le zero_le_one] at hr
  -- mean value theorem for `m ↦ ∂_e g_s(m − y)` on the ball `‖m‖ ≤ ρ`
  set K := gkB (t / 2) * Real.exp (ρ ^ 2 / (4 * (t / 2))) * Real.exp (-‖y‖ ^ 2 / (8 * (t / 2)))
    with hK
  have hK0 : 0 ≤ K := by rw [hK]; unfold gkB; positivity
  have hmem : ∀ (x : ℂ) (h : ℝ), ‖x‖ + |h| ≤ ρ → x + (r * h) • e ∈ Metric.closedBall (0 : ℂ) ρ := by
    intro x h hxh
    rw [Metric.mem_closedBall, dist_zero_right]
    have : ‖(r * h) • e‖ ≤ |h| := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hr.1]
      calc r * |h| * ‖e‖ ≤ 1 * |h| * 1 := by gcongr; exact hr.2
        _ = |h| := by ring
    exact (norm_add_le _ _).trans (by linarith)
  have hmv := (convex_closedBall (0 : ℂ) ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun m => gkD (t / 2) e (m - y)) (f' := fun m => gkDD (t / 2) e (m - y)) (C := K)
    (fun m _ => by
      have := (hasFDerivAt_gkD hs.ne' e (m - y)).comp m ((hasFDerivAt_id m).sub_const y)
      rw [ContinuousLinearMap.comp_id] at this
      exact this.hasFDerivWithinAt)
    (fun m hm => by
      refine (norm_gkDD_le hs he _).trans ?_
      rw [hK, mul_assoc]
      refine mul_le_mul_of_nonneg_left (exp_shift_le hs ?_) (by unfold gkB; positivity)
      rw [Metric.mem_closedBall, dist_zero_right] at hm
      simpa using hm)
    (hmem x' h' hxh') (hmem x h hxh)
  have e1 : ∀ (x : ℂ) (h : ℝ), x - y + (r * h) • e = (x + (r * h) • e) - y := fun _ _ => by abel
  rw [e1, e1]
  refine hmv.trans (mul_le_mul_of_nonneg_left ?_ hK0)
  calc ‖x + (r * h) • e - (x' + (r * h') • e)‖ = ‖(x - x') + (r * (h - h')) • e‖ := by
        congr 1; rw [mul_sub, sub_smul]; abel
    _ ≤ ‖x - x'‖ + ‖(r * (h - h')) • e‖ := norm_add_le _ _
    _ ≤ ‖x - x'‖ + |h - h'| := by
        gcongr
        rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hr.1]
        calc r * |h - h'| * ‖e‖ ≤ 1 * |h - h'| * 1 := by gcongr; exact hr.2
          _ = |h - h'| := by ring

end WhiteNoise
end LQGMetric
