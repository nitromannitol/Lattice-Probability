/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L7Meas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatMeas

/-!
# Measurability of `p_{A ∩ B(c, r)}` in all parameters, including the radius (P2-DZZPRE, WP-112)

DZZ's truncated field `η` (eq:WND_decomposition-approximation, `LBM_LGDarXiv.tex` l. 444–447)
integrates `p_{𝕍 ∩ B_{r(s)}(v)}(s/2; v, w)` against white noise, with a radius `r(s)` depending on
the time variable. Its kernel is jointly measurable in `(s, w)`: `measurable_killedHeat_inter_ball`
extends `KilledHeat.measurable_killedHeat` (D53) to domains `A ∩ B(c(a), r(a))` with measurable
centre and radius. Own bookkeeping (the paper does not discuss measurability): the countable
description `cEvent` of the bridge event uses `innerSet (A ∩ B(c, r)) n = innerSet A n ∩
{y | |y − c| + 1/(n+1) ≤ r}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace LQGMetric
namespace DZZ

open KilledHeat

lemma innerSet_inter (A B : Set ℂ) (n : ℕ) :
    innerSet (A ∩ B) n = innerSet A n ∩ innerSet B n := by
  ext x
  simp [innerSet, subset_inter_iff]

/-- `B(y, ε) ⊆ B(c, r)` iff `|y − c| + ε ≤ r` (for `ε > 0`, in `ℂ`). -/
lemma ball_subset_ball_iff' {y c : ℂ} {ε r : ℝ} (hε : 0 < ε) :
    Metric.ball y ε ⊆ Metric.ball c r ↔ dist y c + ε ≤ r := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    set τ := max 0 (r - dist y c) with hτ
    have hτ0 : 0 ≤ τ := le_max_left _ _
    have hτε : τ < ε := max_lt hε (by linarith)
    -- a unit vector pointing away from `c`
    set e : ℂ := if y = c then 1 else (y - c) / ((‖y - c‖ : ℝ) : ℂ) with he
    have hy : ‖y - c + (τ : ℂ) * e‖ = ‖y - c‖ + τ := by
      by_cases hyc : y = c
      · simp [he, hyc, abs_of_nonneg hτ0]
      · have hn : (‖y - c‖ : ℝ) ≠ 0 := by simpa [sub_eq_zero] using hyc
        have : y - c + (τ : ℂ) * e = (((‖y - c‖ + τ) / ‖y - c‖ : ℝ) : ℂ) * (y - c) := by
          have hn' : ((‖y - c‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
          simp only [he, if_neg hyc]
          push_cast
          field_simp <;> ring
        rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
        field_simp
    have hz : y + (τ : ℂ) * e ∈ Metric.ball y ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      have he1 : ‖e‖ = 1 := by
        by_cases hyc : y = c
        · simp [he, hyc]
        · have hn : (‖y - c‖ : ℝ) ≠ 0 := by simpa [sub_eq_zero] using hyc
          simp only [he, if_neg hyc, norm_div, Complex.norm_real, Real.norm_eq_abs,
            abs_norm]
          field_simp
      simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hτ0, he1, mul_one]
      exact hτε
    have := h hz
    rw [Metric.mem_ball, dist_eq_norm, show y + (τ : ℂ) * e - c = y - c + (τ : ℂ) * e by ring,
      hy, ← dist_eq_norm] at this
    have : r - dist y c ≤ τ := le_max_right _ _
    linarith
  · intro h z hz
    rw [Metric.mem_ball] at hz ⊢
    linarith [dist_triangle z y c]

lemma innerSet_ball (c : ℂ) (r : ℝ) (n : ℕ) :
    innerSet (Metric.ball c r) n = {y | dist y c + 1 / ((n : ℝ) + 1) ≤ r} := by
  ext y
  simp only [innerSet, mem_setOf_eq]
  exact ball_subset_ball_iff' (by positivity)

lemma measurableSet_cEvent_inter_ball {α : Type*} {mα : MeasurableSpace α} (A : Set ℂ)
    (t : ℝ≥0) {g : α → (Bool × ℚ → ℝ)} {f h c : α → ℂ} {r : α → ℝ} (hg : Measurable g)
    (hf : Measurable f) (hh : Measurable h) (hc : Measurable c) (hr : Measurable r) :
    MeasurableSet {p : α | g p ∈ cEvent (A ∩ Metric.ball (c p) (r p)) t (f p) (h p)} := by
  have : {p : α | g p ∈ cEvent (A ∩ Metric.ball (c p) (r p)) t (f p) (h p)} = ⋃ n : ℕ, ⋂ q : ℚ,
      ({p | f p + ((((clampT t q : ℝ≥0) : ℝ) / t : ℝ) : ℂ) * (h p - f p) + cpt (g p) q ∈
        innerSet A n} ∩
      {p | dist (f p + ((((clampT t q : ℝ≥0) : ℝ) / t : ℝ) : ℂ) * (h p - f p) + cpt (g p) q)
        (c p) + 1 / ((n : ℝ) + 1) ≤ r p}) := by
    ext p
    simp [cEvent, innerSet_inter, innerSet_ball]
  rw [this]
  refine MeasurableSet.iUnion fun n ↦ MeasurableSet.iInter fun q ↦ ?_
  have hm : Measurable fun p : α ↦
      f p + ((((clampT t q : ℝ≥0) : ℝ) / t : ℝ) : ℂ) * (h p - f p) + cpt (g p) q := by
    unfold cpt
    fun_prop
  refine (hm (isClosed_innerSet A n).measurableSet).inter ?_
  exact measurableSet_le ((hm.dist hc).add_const _) hr

/-- **Joint measurability** of `a ↦ p_{A ∩ B(c(a), r(a))}(t(a); z(a), w(a))`, `A` open. -/
theorem measurable_killedHeat_inter_ball {α : Type*} {mα : MeasurableSpace α} {A : Set ℂ}
    (hA : IsOpen A) {T : α → ℝ≥0} {c z w : α → ℂ} {r : α → ℝ} (hT : Measurable T)
    (hc : Measurable c) (hr : Measurable r) (hz : Measurable z) (hw : Measurable w) :
    Measurable fun a ↦ killedHeat (A ∩ Metric.ball (c a) (r a)) (T a) (z a) (w a) := by
  set μ1 := P2.map (fun ω p ↦ sampled 1 (stdBridge 1) p ω)
  have hS : MeasurableSet {q : α × (Bool × ℚ → ℝ) |
      (fun p ↦ Real.sqrt (T q.1) * q.2 p) ∈
        cEvent (A ∩ Metric.ball (c q.1) (r q.1)) 1 (z q.1) (w q.1)} :=
    measurableSet_cEvent_inter_ball A 1 (by fun_prop) (hz.comp measurable_fst)
      (hw.comp measurable_fst) (hc.comp measurable_fst) (hr.comp measurable_fst)
  have hF : Measurable fun a ↦ (μ1 {g | (fun p ↦ Real.sqrt (T a) * g p) ∈
      cEvent (A ∩ Metric.ball (c a) (r a)) 1 (z a) (w a)}).toReal :=
    (measurable_measure_prodMk_left hS).ennreal_toReal
  have hH : Measurable fun a ↦ heatKernel (T a) (z a) (w a) := by
    unfold heatKernel
    fun_prop
  have e : (fun a ↦ killedHeat (A ∩ Metric.ball (c a) (r a)) (T a) (z a) (w a)) = fun a ↦
      heatKernel (T a) (z a) (w a) * (μ1 {g | (fun p ↦ Real.sqrt (T a) * g p) ∈
        cEvent (A ∩ Metric.ball (c a) (r a)) 1 (z a) (w a)}).toReal := by
    funext a
    rcases eq_or_ne (T a) 0 with h0 | h0
    · simp [killedHeat, heatKernel, h0]
    · rw [killedHeat, bridgeStay_eq_scale (hA.inter Metric.isOpen_ball) h0]
  rw [e]
  exact hH.mul hF

end DZZ
end LQGMetric
