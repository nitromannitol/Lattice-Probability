/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.HeatDirTime at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# DGo (3.1): the two scalar estimates behind `ĥ^D_δ(v) ∈ L²` (task P2-HEAT1, packet R0)

Ding–Goswami, arXiv:1610.09998, `Watabiki_final.tex`, (3.1) (DGo:491–494): the white-noise field
`ĥ^𝒰_δ(v) = √π ∫ (2π)⁻¹∫ p^𝒰(s/2; v + δe^{iθ}, w) dθ W(dw, ds)` requires the circle average of the
heat kernel to be square integrable in `(s, w)`; by Chapman–Kolmogorov this is the finiteness of
`∫_0^T (2π)⁻²∫∫ p_s(v + δe^{iθ}, v + δe^{iθ'}) dθ dθ' ds`, i.e. the logarithmic singularity of the
time-integrated heat kernel (DGo (eq:Green_fxn), DGo:479–486: `π∫_0^∞ p^𝒰_s = G_𝒰 ∼ log(1/|x−y|)`)
is integrable on the circle. Here:

* `heatKernel_le_inv_sq` / `heatKernel_le_inv_time` — `p_s(x,y) ≤ (π|x−y|²)⁻¹`, `p_s(x,y) ≤ (2πs)⁻¹`.
* `lintegral_heatKernel_time_le` — `∫_0^T p_s(x,y) ds ≤ 1/π + (2π)⁻¹(|log T| + 2|log|x−y||)`.
* `integral_abs_log_circle_le` — `∫_0^{2π} |log|v + δe^{iθ} − a|| dθ ≤ 2π(2 log⁺(|v−a|+δ) − log δ)`,
  from mathlib's Jensen-type identity `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`.

Both are own elementary estimates (the paper uses them implicitly); proposed DEVIATIONS entry
HEAT1-1.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Real Set
open scoped ENNReal Interval

namespace LQGMetric
namespace DGo
namespace HeatDir

/-- `p_s(x,y) ≤ (π|x−y|²)⁻¹` for `s > 0`, `x ≠ y` (from `e^{−u} ≤ 1/u`). -/
lemma heatKernel_le_inv_sq {s : ℝ} (hs : 0 < s) {x y : ℂ} (hr : 0 < ‖x - y‖) :
    heatKernel s x y ≤ (π * ‖x - y‖ ^ 2)⁻¹ := by
  set r := ‖x - y‖
  set u := r ^ 2 / (2 * s) with hu
  have hu0 : 0 < u := by positivity
  have he : Real.exp (-u) * u ≤ 1 := by
    have h1 := Real.add_one_le_exp u
    rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos u)] <;> linarith
  unfold heatKernel
  rw [show -‖x - y‖ ^ 2 / (2 * s) = -u by rw [hu]; ring]
  have : (π * r ^ 2)⁻¹ = (2 * π * s)⁻¹ * u⁻¹ := by
    rw [hu]; field_simp
  rw [this]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [inv_eq_one_div, le_div_iff₀ hu0]; exact he

/-- `p_s(x,y) ≤ (2πs)⁻¹` for `s > 0`. -/
lemma heatKernel_le_inv_time {s : ℝ} (hs : 0 < s) (x y : ℂ) :
    heatKernel s x y ≤ (2 * π)⁻¹ * s⁻¹ := by
  unfold heatKernel
  rw [show (2 * π)⁻¹ * s⁻¹ = (2 * π * s)⁻¹ * 1 by rw [mul_inv]; ring]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Real.exp_le_one_iff]
  have : 0 ≤ ‖x - y‖ ^ 2 / (2 * s) := by positivity
  rw [neg_div]; linarith

/-- **Time integral of the heat kernel**:
`∫_0^T p_s(x,y) ds ≤ 1/π + (2π)⁻¹(|log T| + 2|log|x−y||)` for `x ≠ y`. -/
theorem lintegral_heatKernel_time_le (T : ℝ) {x y : ℂ} (hr : 0 < ‖x - y‖) :
    ∫⁻ s in Ioc 0 T, ENNReal.ofReal (heatKernel s x y) ≤
      ENNReal.ofReal (1 / π + (2 * π)⁻¹ * (|Real.log T| + 2 * |Real.log ‖x - y‖|)) := by
  set r := ‖x - y‖
  have hr2 : 0 < r ^ 2 := by positivity
  set M := max T (r ^ 2)
  have hM : r ^ 2 ≤ M := le_max_right _ _
  have hsub : Ioc 0 T ⊆ Ioc 0 (r ^ 2) ∪ Ioc (r ^ 2) M := by
    rw [Ioc_union_Ioc_eq_Ioc hr2.le hM]; exact Ioc_subset_Ioc_right (le_max_left _ _)
  have h1 : ∫⁻ s in Ioc 0 (r ^ 2), ENNReal.ofReal (heatKernel s x y) ≤ ENNReal.ofReal (1 / π) := by
    calc ∫⁻ s in Ioc 0 (r ^ 2), ENNReal.ofReal (heatKernel s x y)
        ≤ ∫⁻ _ in Ioc 0 (r ^ 2), ENNReal.ofReal ((π * r ^ 2)⁻¹) :=
          setLIntegral_mono measurable_const fun s hs =>
            ENNReal.ofReal_le_ofReal (heatKernel_le_inv_sq hs.1 hr)
      _ = ENNReal.ofReal (1 / π) := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; field_simp
  have hint : IntegrableOn (fun s : ℝ => (2 * π)⁻¹ * s⁻¹) (Ioc (r ^ 2) M) := by
    have : IntervalIntegrable (fun s : ℝ => (2 * π)⁻¹ * s⁻¹) volume (r ^ 2) M :=
      (intervalIntegral.intervalIntegrable_inv (fun s hs => by
        rw [Set.uIcc_of_le hM] at hs; exact (hr2.trans_le hs.1).ne') continuousOn_id
        |>.const_mul _)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hM).1 this
  have h2 : ∫⁻ s in Ioc (r ^ 2) M, ENNReal.ofReal (heatKernel s x y) ≤
      ENNReal.ofReal ((2 * π)⁻¹ * (|Real.log T| + 2 * |Real.log r|)) := by
    calc ∫⁻ s in Ioc (r ^ 2) M, ENNReal.ofReal (heatKernel s x y)
        ≤ ∫⁻ s in Ioc (r ^ 2) M, ENNReal.ofReal ((2 * π)⁻¹ * s⁻¹) :=
          setLIntegral_mono' measurableSet_Ioc fun s hs =>
            ENNReal.ofReal_le_ofReal (heatKernel_le_inv_time (hr2.trans hs.1) x y)
      _ = ENNReal.ofReal (∫ s in Ioc (r ^ 2) M, (2 * π)⁻¹ * s⁻¹) :=
          (ofReal_integral_eq_lintegral_ofReal hint
            (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs =>
              by have := hr2.trans hs.1; positivity)).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← intervalIntegral.integral_of_le hM, intervalIntegral.integral_const_mul,
            integral_inv_of_pos hr2 (hr2.trans_le hM)]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [Real.log_div (hr2.trans_le hM).ne' hr2.ne', Real.log_pow]
          have key : Real.log M - 2 * Real.log r ≤ |Real.log T| + 2 * |Real.log r| := by
            rcases le_total T (r ^ 2) with h | h
            · have hM' : M = r ^ 2 := max_eq_right h
              rw [hM', Real.log_pow]; push_cast
              nlinarith [abs_nonneg (Real.log r), abs_nonneg (Real.log T)]
            · have hM' : M = T := max_eq_left h
              rw [hM']
              nlinarith [le_abs_self (Real.log T), neg_abs_le (Real.log r)]
          push_cast
          linarith
  calc ∫⁻ s in Ioc 0 T, ENNReal.ofReal (heatKernel s x y)
      ≤ ∫⁻ s in Ioc 0 (r ^ 2) ∪ Ioc (r ^ 2) M, ENNReal.ofReal (heatKernel s x y) :=
        lintegral_mono_set hsub
    _ ≤ (∫⁻ s in Ioc 0 (r ^ 2), ENNReal.ofReal (heatKernel s x y)) +
          ∫⁻ s in Ioc (r ^ 2) M, ENNReal.ofReal (heatKernel s x y) := lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal (1 / π) + ENNReal.ofReal ((2 * π)⁻¹ * (|Real.log T| + 2 * |Real.log r|)) :=
        add_le_add h1 h2
    _ = _ := (ENNReal.ofReal_add (by positivity) (by positivity)).symm

/-- **Integrability of the logarithm on a circle**, uniformly in the base point:
`∫_0^{2π} |log|v + δe^{iθ} − a|| dθ ≤ 2π(2 log⁺(|v−a|+δ) − log δ)` for `δ > 0`. -/
theorem integral_abs_log_circle_le {δ : ℝ} (hδ : 0 < δ) (v a : ℂ) :
    ∫ θ in (0 : ℝ)..2 * π, |Real.log ‖circleMap v δ θ - a‖| ≤
      2 * π * (2 * log⁺ (‖v - a‖ + δ) - Real.log δ) := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hI : IntervalIntegrable (fun θ => Real.log ‖circleMap v δ θ - a‖) volume 0 (2 * π) :=
    circleIntegrable_log_norm_sub_const (a := a) (c := v) δ
  set C0 := log⁺ (‖v - a‖ + δ)
  have hpt : ∀ θ, |Real.log ‖circleMap v δ θ - a‖| ≤ 2 * C0 - Real.log ‖circleMap v δ θ - a‖ := by
    intro θ
    have hn : ‖circleMap v δ θ - a‖ ≤ ‖v - a‖ + δ := by
      calc ‖circleMap v δ θ - a‖ = ‖(circleMap v δ θ - v) + (v - a)‖ := by ring_nf
        _ ≤ ‖circleMap v δ θ - v‖ + ‖v - a‖ := norm_add_le _ _
        _ = δ + ‖v - a‖ := by rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hδ]
        _ = _ := add_comm _ _
    have hp : Real.log ‖circleMap v δ θ - a‖ ≤ C0 :=
      (le_max_right 0 _).trans
        (Real.posLog_le_posLog ((neg_one_lt_zero.le).trans (norm_nonneg _)) hn)
    have hC0 : 0 ≤ C0 := Real.posLog_nonneg
    rcases le_total 0 (Real.log ‖circleMap v δ θ - a‖) with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_nonpos h]; linarith
  have hmono := intervalIntegral.integral_mono_on h2π hI.abs
    (intervalIntegrable_const.sub hI) fun θ _ => hpt θ
  rw [intervalIntegral.integral_sub intervalIntegrable_const hI,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
  have havg := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := a) (c := v)
    hδ.ne'
  rw [Real.circleAverage_def] at havg
  have hlow : 2 * π * Real.log δ ≤ ∫ θ in (0 : ℝ)..2 * π, Real.log ‖circleMap v δ θ - a‖ := by
    have hpos : 0 < 2 * π := by positivity
    have : ∫ θ in (0 : ℝ)..2 * π, Real.log ‖circleMap v δ θ - a‖ =
        2 * π * (Real.log δ + log⁺ (δ⁻¹ * ‖v - a‖)) := by
      rw [← havg, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    rw [this]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right Real.posLog_nonneg) hpos.le
  linarith

end HeatDir
end DGo
end LQGMetric
