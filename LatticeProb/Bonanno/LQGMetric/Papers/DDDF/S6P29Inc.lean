/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P29Inc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareL1
import Mathlib.Analysis.Calculus.MeanValue

/-!
# DDDF Prop 29, first-term increments: one-dimensional `L¹` shift bounds (task P2-DDDFP29c)

DDDF arXiv:1904.08021, `tightness.tex` DD:1571–1576 bounds the increments of the first term of
(6.97) by "splitting the integral at `√|x−x'|`, (6.96) for small `s`, gradient estimates for
larger `s`". (6.96) is not uniform near `∂D` (see `P29First`), so we use an own `L¹` route
(see `S6P29Inc2`). Here are the one-dimensional inputs, for `r > 0`, `c₀ = 2e^{1/4}`:

* `gaussShift_lintegral_le`: `∫_ℝ |g_r(u − v) − g_r(u' − v)| dv ≤ c₀ |u − u'| / √r`
  (mean value theorem with `|g_r'(ξ)| ≤ c₀ r^{-1/2} g_{4r}(u − v)` when `|u − u'| ≤ √r`, and
  the trivial bound `2` otherwise);
* `intervalShift_lintegral_le`: the same for the image-series kernel,
  `∫_{(a,a+L]} |q_r(u,v) − q_r(u',v)| dv ≤ c₀ |u − u'| / √r`, for all `u, u'` (folding,
  `HeatSq.lintegral_fold`);
* `clampI`, `intervalDirKernel_clampI`: `q_r(clamp u, v) = 0` off `(a, a+L)`.

Own elementary proofs (DEVIATIONS: replaces DD:1571–1576).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace P29WN

open HeatSq

/-- The constant `c₀ = 2 e^{1/4}`. -/
def incConst : ℝ := 2 * Real.exp (1 / 4)

lemma two_le_incConst : 2 ≤ incConst := by
  unfold incConst; have := Real.one_le_exp (show (0 : ℝ) ≤ 1 / 4 by norm_num); linarith

lemma hasDerivAt_gauss1 {r : ℝ} (hr : 0 < r) (ξ : ℝ) :
    HasDerivAt (gauss1 r) (gauss1 r ξ * (-ξ / r)) ξ := by
  have h1 : HasDerivAt (fun x : ℝ => -x ^ 2 / (2 * r)) (-1 / (2 * r) * (↑2 * ξ ^ (2 - 1))) ξ := by
    have := (hasDerivAt_pow 2 ξ).const_mul (-1 / (2 * r))
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  have h := h1.exp.const_mul (Real.sqrt (2 * π * r))⁻¹
  show HasDerivAt (fun z => (Real.sqrt (2 * π * r))⁻¹ * Real.exp (-z ^ 2 / (2 * r))) _ ξ
  refine h.congr_deriv ?_
  unfold gauss1
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  field_simp

/-- `|ξ| e^{−ξ²/(2r)} ≤ √r e^{1/4 − b²/(8r)}` when `(ξ − b)² ≤ r`. -/
lemma abs_mul_exp_le {r ξ b : ℝ} (hr : 0 < r) (hξ : (ξ - b) ^ 2 ≤ r) :
    |ξ| * Real.exp (-ξ ^ 2 / (2 * r)) ≤ Real.sqrt r * Real.exp (1 / 4 - b ^ 2 / (8 * r)) := by
  have hs := Real.sqrt_pos.mpr hr
  have hss : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have h1 : |ξ| ≤ Real.sqrt r * Real.exp (ξ ^ 2 / (4 * r)) := by
    have hx2 : (|ξ| / Real.sqrt r) ^ 2 = ξ ^ 2 / r := by rw [div_pow, sq_abs, hss]
    have hx : |ξ| / Real.sqrt r ≤ 1 + ξ ^ 2 / (4 * r) := by
      rw [show ξ ^ 2 / (4 * r) = (|ξ| / Real.sqrt r) ^ 2 / 4 by rw [hx2]; ring]
      nlinarith [sq_nonneg (|ξ| / Real.sqrt r / 2 - 1)]
    have := Real.add_one_le_exp (ξ ^ 2 / (4 * r))
    rw [div_le_iff₀ hs] at hx
    nlinarith
  calc |ξ| * Real.exp (-ξ ^ 2 / (2 * r))
      ≤ Real.sqrt r * Real.exp (ξ ^ 2 / (4 * r)) * Real.exp (-ξ ^ 2 / (2 * r)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.sqrt r * Real.exp (-ξ ^ 2 / (4 * r)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; field_simp; ring
    _ ≤ Real.sqrt r * Real.exp (1 / 4 - b ^ 2 / (8 * r)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hs.le
        rw [div_sub_div _ _ (by norm_num) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith [sq_nonneg (ξ + b - ξ - ξ), sq_nonneg (2 * ξ - b)]

/-- Derivative bound `|g_r'(ξ)| ≤ c₀ r^{-1/2} g_{4r}(b)` for `(ξ − b)² ≤ r`. -/
lemma abs_deriv_gauss1_le {r ξ b : ℝ} (hr : 0 < r) (hξ : (ξ - b) ^ 2 ≤ r) :
    ‖gauss1 r ξ * (-ξ / r)‖ ≤ incConst / Real.sqrt r * gauss1 (4 * r) b := by
  have hs := Real.sqrt_pos.mpr hr
  have h := abs_mul_exp_le hr hξ
  have e8 : Real.sqrt (2 * π * (4 * r)) = 2 * Real.sqrt (2 * π * r) := by
    rw [show 2 * π * (4 * r) = 2 ^ 2 * (2 * π * r) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have hsr : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have hp := Real.sqrt_pos.mpr (show 0 < 2 * π * r by positivity)
  rw [Real.norm_eq_abs]
  unfold gauss1 incConst
  rw [e8, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hp), abs_of_pos (Real.exp_pos _),
    abs_div, abs_neg, abs_of_pos hr]
  have e1 : Real.exp (1 / 4 - b ^ 2 / (8 * r)) = Real.exp (1 / 4) * Real.exp (-b ^ 2 / (2 * (4 * r))) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [e1] at h
  rw [show (Real.sqrt (2 * π * r))⁻¹ * Real.exp (-ξ ^ 2 / (2 * r)) * (|ξ| / r) =
      (Real.sqrt (2 * π * r))⁻¹ / r * (|ξ| * Real.exp (-ξ ^ 2 / (2 * r))) by ring]
  calc (Real.sqrt (2 * π * r))⁻¹ / r * (|ξ| * Real.exp (-ξ ^ 2 / (2 * r)))
      ≤ (Real.sqrt (2 * π * r))⁻¹ / r *
          (Real.sqrt r * (Real.exp (1 / 4) * Real.exp (-b ^ 2 / (2 * (4 * r))))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by
        generalize Real.sqrt (2 * π * r) = P at *
        generalize hS : Real.sqrt r = S at *
        subst hsr
        field_simp

/-- Pointwise shift bound for `|u − u'| ≤ √r`. -/
lemma abs_gauss1_shift_le {r u u' v : ℝ} (hr : 0 < r) (hδ : (u - u') ^ 2 ≤ r) :
    |gauss1 r (u - v) - gauss1 r (u' - v)| ≤
      incConst / Real.sqrt r * |u - u'| * gauss1 (4 * r) (u - v) := by
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := gauss1 r)
    (f' := fun ξ => gauss1 r ξ * (-ξ / r)) (s := uIcc (u' - v) (u - v))
    (C := incConst / Real.sqrt r * gauss1 (4 * r) (u - v))
    (fun ξ _ => (hasDerivAt_gauss1 hr ξ).hasDerivWithinAt)
    (fun ξ hξ => by
      refine abs_deriv_gauss1_le hr (le_trans ?_ hδ)
      rw [← sq_abs, ← sq_abs (u - u')]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      rcases le_total (u' - v) (u - v) with h | h
      · rw [uIcc_of_le h] at hξ
        rw [abs_of_nonpos (by linarith [hξ.2]), abs_of_nonneg (by linarith)]; linarith [hξ.1]
      · rw [uIcc_of_ge h] at hξ
        rw [abs_of_nonneg (by linarith [hξ.1]), abs_of_nonpos (by linarith)]; linarith [hξ.2])
    (convex_uIcc _ _) left_mem_uIcc right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs, show u - v - (u' - v) = u - u' by ring] at hmvt
  linarith

/-- **`L¹` shift bound for the Gaussian**: `∫ |g_r(u−v) − g_r(u'−v)| dv ≤ c₀|u−u'|/√r`. -/
theorem gaussShift_lintegral_le {r : ℝ} (hr : 0 < r) (u u' : ℝ) :
    ∫⁻ v, ENNReal.ofReal |gauss1 r (u - v) - gauss1 r (u' - v)| ≤
      ENNReal.ofReal (incConst / Real.sqrt r * |u - u'|) := by
  have hs := Real.sqrt_pos.mpr hr
  rcases le_or_gt ((u - u') ^ 2) r with hδ | hδ
  · calc _ ≤ ∫⁻ v, ENNReal.ofReal (incConst / Real.sqrt r * |u - u'|) *
            ENNReal.ofReal (gauss1 (4 * r) (u - v)) := by
          refine lintegral_mono fun v => ?_
          rw [← ENNReal.ofReal_mul (by unfold incConst; positivity)]
          exact ENNReal.ofReal_le_ofReal (abs_gauss1_shift_le hr hδ)
      _ = _ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_ofReal_gauss1_sub (by positivity), mul_one]
  · have h1 : 2 ≤ incConst / Real.sqrt r * |u - u'| := by
      have hlt : Real.sqrt r < |u - u'| := by
        rw [← Real.sqrt_sq (abs_nonneg (u - u')), sq_abs]
        exact Real.sqrt_lt_sqrt hr.le hδ
      rw [div_mul_eq_mul_div, le_div_iff₀ hs]
      nlinarith [two_le_incConst]
    calc _ ≤ ∫⁻ v, (ENNReal.ofReal (gauss1 r (u - v)) + ENNReal.ofReal (gauss1 r (u' - v))) := by
          refine lintegral_mono fun v => ?_
          rw [← ENNReal.ofReal_add (gauss1_nonneg _ _) (gauss1_nonneg _ _)]
          refine ENNReal.ofReal_le_ofReal ((abs_sub _ _).trans ?_)
          rw [abs_of_nonneg (gauss1_nonneg _ _), abs_of_nonneg (gauss1_nonneg _ _)]
      _ = 2 := by
          rw [lintegral_add_left (f := fun v => ENNReal.ofReal (gauss1 r (u - v)))
            (ENNReal.measurable_ofReal.comp
            ((continuous_gauss1 r).comp (continuous_sub_left u)).measurable),
            lintegral_ofReal_gauss1_sub hr, lintegral_ofReal_gauss1_sub hr, one_add_one_eq_two]
      _ ≤ _ := by rw [← ENNReal.ofReal_ofNat 2]; exact ENNReal.ofReal_le_ofReal h1

/-- Pointwise: the image-series difference is dominated by the two folded families. -/
lemma ofReal_abs_intervalDirKernel_sub_le {a L r : ℝ} (hr : 0 < r) (hL : 0 < L) (u u' v : ℝ) :
    ENNReal.ofReal |intervalDirKernel a L r u v - intervalDirKernel a L r u' v| ≤
      (∑' n : ℤ, ENNReal.ofReal |gauss1 r (u - v + 2 * n * L) - gauss1 r (u' - v + 2 * n * L)|) +
      ∑' n : ℤ, ENNReal.ofReal |gauss1 r (u + v - 2 * a + 2 * n * L) -
        gauss1 r (u' + v - 2 * a + 2 * n * L)| := by
  have hS := fun c => summable_gauss1_shift (L := L) hr hL c
  rw [intervalDirKernel_eq_sub hr hL, intervalDirKernel_eq_sub hr hL,
    show ∀ p q p' q' : ℝ, p - q - (p' - q') = (p - p') - (q - q') by intros; ring,
    ← (hS (u - v)).tsum_sub (hS (u' - v)), ← (hS (u + v - 2 * a)).tsum_sub (hS (u' + v - 2 * a))]
  refine (ENNReal.ofReal_le_ofReal (abs_sub _ _)).trans ?_
  rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  refine add_le_add ?_ ?_
  · rw [← Real.enorm_eq_ofReal_abs]
    refine enorm_tsum_le_tsum_enorm.trans (le_of_eq ?_)
    congr 1; funext n; rw [Real.enorm_eq_ofReal_abs]
  · rw [← Real.enorm_eq_ofReal_abs]
    refine enorm_tsum_le_tsum_enorm.trans (le_of_eq ?_)
    congr 1; funext n; rw [Real.enorm_eq_ofReal_abs]

/-- **`L¹` shift bound for the image-series kernel**, for all `u, u'`. -/
theorem intervalShift_lintegral_le {a L r : ℝ} (hr : 0 < r) (hL : 0 < L) (u u' : ℝ) :
    ∫⁻ v in Ioc a (a + L), ENNReal.ofReal |intervalDirKernel a L r u v -
        intervalDirKernel a L r u' v| ≤
      ENNReal.ofReal (incConst / Real.sqrt r * |u - u'|) := by
  set h : ℝ → ℝ≥0∞ := fun w => ENNReal.ofReal |gauss1 r (u - w) - gauss1 r (u' - w)| with hh
  have hfold := lintegral_fold (a := a) hL h
  have hc := continuous_gauss1 r
  have hmeas : ∀ f f' : ℝ → ℝ, Continuous f → Continuous f' → AEMeasurable
      (fun w => ENNReal.ofReal |gauss1 r (f w) - gauss1 r (f' w)|)
      (volume.restrict (Ioc a (a + L))) := fun f f' hf hf' =>
    (ENNReal.measurable_ofReal.comp (continuous_abs.comp ((hc.comp hf).sub
      (hc.comp hf'))).measurable).aemeasurable
  refine (lintegral_mono fun v => ofReal_abs_intervalDirKernel_sub_le hr hL u u' v).trans ?_
  have hm : ∀ f f' : ℝ → ℝ, Continuous f → Continuous f' →
      Measurable (fun w => ENNReal.ofReal |gauss1 r (f w) - gauss1 r (f' w)|) := fun f f' hf hf' =>
    ENNReal.measurable_ofReal.comp (continuous_abs.comp ((hc.comp hf).sub (hc.comp hf'))).measurable
  rw [lintegral_add_left (f := fun v => ∑' n : ℤ,
    ENNReal.ofReal |gauss1 r (u - v + 2 * n * L) - gauss1 r (u' - v + 2 * n * L)|)
    (Measurable.ennreal_tsum fun n : ℤ => hm _ _ (by fun_prop) (by fun_prop))]
  rw [lintegral_tsum fun n : ℤ => hmeas (fun w => u - w + 2 * n * L) (fun w => u' - w + 2 * n * L)
      (by fun_prop) (by fun_prop),
    lintegral_tsum fun n : ℤ => hmeas (fun w => u + w - 2 * a + 2 * n * L)
      (fun w => u' + w - 2 * a + 2 * n * L) (by fun_prop) (by fun_prop)]
  refine le_trans (le_of_eq ?_) (hfold.le.trans (gaussShift_lintegral_le hr u u'))
  congr 1
  · rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => ∫⁻ w in Ioc a (a + L), h (w + 2 * n * L))]
    congr 1; funext n; congr 1; funext w
    simp only [hh, Equiv.neg_apply, Int.cast_neg]; congr 3 <;> ring
  · rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => ∫⁻ w in Ioc a (a + L), h (2 * a - w + 2 * n * L))]
    congr 1; funext n; congr 1; funext w
    simp only [hh, Equiv.neg_apply, Int.cast_neg]; congr 3 <;> ring

/-- Clamping to `[a, a+L]`. -/
def clampI (a L u : ℝ) : ℝ := max a (min u (a + L))

lemma abs_clampI_sub_le (a L u u' : ℝ) : |clampI a L u - clampI a L u'| ≤ |u - u'| := by
  unfold clampI
  rw [max_comm a, max_comm a]
  refine (abs_max_sub_max_le_abs (min u (a + L)) (min u' (a + L)) a).trans ?_
  refine (abs_min_sub_min_le_max u (a + L) u' (a + L)).trans ?_
  simp

lemma clampI_of_mem {a L u : ℝ} (hu : u ∈ Ioo a (a + L)) : clampI a L u = u := by
  unfold clampI; rw [min_eq_left hu.2.le, max_eq_right hu.1.le]

/-- `q_r(clamp u, v) = 0` for `u ∉ (a, a+L)`. -/
lemma intervalDirKernel_clampI_of_not_mem {a L r u : ℝ} (hr : 0 < r) (hL : 0 < L)
    (hu : u ∉ Ioo a (a + L)) (v : ℝ) : intervalDirKernel a L r (clampI a L u) v = 0 := by
  unfold clampI
  rcases le_or_gt u a with h | h
  · rw [max_eq_left ((min_le_left _ _).trans h)]; exact intervalDirKernel_left hr hL v
  · have h2 : a + L ≤ u := by
      by_contra h3; exact hu ⟨h, lt_of_not_ge h3⟩
    rw [min_eq_right h2, max_eq_right (by linarith)]; exact intervalDirKernel_right hr hL v

end P29WN
end DDDF
end LQGMetric
