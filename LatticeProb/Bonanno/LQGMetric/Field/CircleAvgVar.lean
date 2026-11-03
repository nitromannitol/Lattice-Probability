/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.CircleAvgVar at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgLimit
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyVar
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The log potential of `circBump` and the variance of the mollified circle averages

`logPot ψ x = ∫ −log|x − y| ψ(y) dy`, so that `logCov φ ψ = ∫ φ · logPot ψ`.
For `Φ_k = circBump k z r`, Fubini and the circle mean value of `log|· − u|`
(mathlib `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`; cf. the core identity
`QuantumZipper.integral_log_norm_sub_circleUnif`, and DS arXiv:0808.1560 §3.1) give
`logPot Φ_k x = −∫ ψ_k(t) g(x − t) dt` with `g(u) = log r + log⁺(|z − u|/r) = log max(r, |z − u|)`
(`logPot_circBump`). Since `g` is `1/r`-Lipschitz, the log potential of the increment
`D = Φ_{n+1} − Φ_n` is `O(2^{-n}/r)` uniformly, hence `logCov D D = ∫ D · logPot D = O(2^{-n}/r)`.
The Lipschitz/L¹–L^∞ bound is an own elementary argument (DS's covariance formula is exact; we
only need the rate).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped Real

namespace LQGMetric
namespace CircleAvg

/-- the log potential `x ↦ ∫ −log|x − y| ψ(y) dy` -/
def logPot (ψ : ℂ → ℝ) (x : ℂ) : ℝ := ∫ y, -Real.log ‖x - y‖ * ψ y

lemma logCov_eq_integral_logPot (φ ψ : ℂ → ℝ) : logCov φ ψ = ∫ x, φ x * logPot ψ x := by
  unfold logCov logPot
  congr 1
  funext x
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

/-- `g_{z,r}(u) = ⨍_{∂B(z,r)} log|a − u| da` -/
def circLog (z : ℂ) (r : ℝ) (u : ℂ) : ℝ := Real.circleAverage (fun a => Real.log ‖a - u‖) z r

lemma circLog_eq {r : ℝ} (hr : r ≠ 0) (z u : ℂ) :
    circLog z r u = Real.log r + Real.posLog (r⁻¹ * ‖z - u‖) :=
  circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hr

lemma posLog_sub_le_abs {A B : ℝ} (hA' : 0 ≤ A) (hB : 0 ≤ B) :
    Real.posLog A - Real.posLog B ≤ |A - B| := by
  have hB' : 0 ≤ Real.posLog B := Real.posLog_nonneg
  rcases le_or_gt A 1 with hA | hA
  · rw [(Real.posLog_eq_zero_iff A).mpr (by rw [abs_of_nonneg hA']; exact hA)]
    linarith [abs_nonneg (A - B)]
  · have hA0 : 0 < A := lt_trans one_pos hA
    rw [Real.posLog_eq_log (by rw [abs_of_pos hA0]; exact hA.le)]
    rcases le_or_gt B 1 with hB1 | hB1
    · rw [(Real.posLog_eq_zero_iff B).mpr (by rw [abs_of_nonneg hB]; exact hB1)]
      have := Real.log_le_sub_one_of_pos hA0
      have : A - 1 ≤ |A - B| := by rw [abs_of_pos (by linarith)]; linarith
      linarith
    · have hB0 : 0 < B := lt_trans one_pos hB1
      rw [Real.posLog_eq_log (by rw [abs_of_pos hB0]; exact hB1.le), ← Real.log_div hA0.ne' hB0.ne']
      have h1 := Real.log_le_sub_one_of_pos (div_pos hA0 hB0)
      have h2 : A / B - 1 ≤ |A - B| := by
        rw [div_sub_one hB0.ne', div_le_iff₀ hB0]
        calc A - B ≤ |A - B| := le_abs_self _
          _ ≤ |A - B| * B := le_mul_of_one_le_right (abs_nonneg _) hB1.le
      linarith

/-- `g_{z,r}` is `1/r`-Lipschitz -/
lemma abs_circLog_sub_le {r : ℝ} (hr : 0 < r) (z u v : ℂ) :
    |circLog z r u - circLog z r v| ≤ ‖u - v‖ / r := by
  have key : ∀ u v : ℂ, circLog z r u - circLog z r v ≤ ‖u - v‖ / r := by
    intro u v
    rw [circLog_eq hr.ne', circLog_eq hr.ne', add_sub_add_left_eq_sub]
    refine (posLog_sub_le_abs (by positivity) (by positivity)).trans ?_
    rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hr), inv_mul_eq_div]
    gcongr
    calc |‖z - u‖ - ‖z - v‖| ≤ ‖(z - u) - (z - v)‖ := abs_norm_sub_norm_le _ _
      _ = ‖u - v‖ := by rw [sub_sub_sub_cancel_left, norm_sub_rev]
  rw [abs_le]
  constructor
  · have := key v u
    rw [norm_sub_rev] at this
    linarith
  · exact key u v

/-! ## Fubini: the log potential of `circBump` -/

section Fubini

variable (k : ℕ) (z : ℂ) (r : ℝ) (x : ℂ)

/-- the angular measure on `(0, 2π]` -/
abbrev μθ : Measure ℝ := volume.restrict (Ioc 0 (2 * π))

lemma circBump_eq_integral (y : ℂ) :
    circBump k z r y = (2 * π)⁻¹ * ∫ θ, bumpTest k 0 (y - circleMap z r θ) ∂μθ := by
  rw [circBump_apply, Real.circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le (by positivity)]
  simp_rw [bumpTest_eq_sub k _ y]

/-- the integrand `(θ, y) ↦ −log|x − y| ψ_k(y − z − r e^{iθ})` -/
def fubF (p : ℝ × ℂ) : ℝ := -Real.log ‖x - p.2‖ * bumpTest k 0 (p.2 - circleMap z r p.1)

/-- the integrand `(θ, t) ↦ ψ_k(t) (−log|z + r e^{iθ} − (x − t)|)` -/
def fubG (p : ℝ × ℂ) : ℝ := bumpTest k 0 p.2 * -Real.log ‖circleMap z r p.1 - (x - p.2)‖

lemma fubG_eq (θ : ℝ) (t : ℂ) : fubG k z r x (θ, t) = fubF k z r x (θ, t + circleMap z r θ) := by
  simp only [fubG, fubF, add_sub_cancel_right]
  rw [mul_comm]
  congr 3
  rw [← norm_neg]
  congr 1
  ring

lemma measurable_fubF : Measurable (fubF k z r x) := by
  unfold fubF
  have h1 : Continuous (bumpTest k 0 : ℂ → ℝ) := (bumpTest k 0).continuous
  have h2 : Continuous fun p : ℝ × ℂ => p.2 - circleMap z r p.1 :=
    continuous_snd.sub ((continuous_circleMap z r).comp continuous_fst)
  exact ((Real.measurable_log.comp (measurable_const.sub measurable_snd).norm).neg).mul
    (h1.comp h2).measurable

lemma measurable_fubG : Measurable (fubG k z r x) := by
  unfold fubG
  have h1 : Continuous (bumpTest k 0 : ℂ → ℝ) := (bumpTest k 0).continuous
  have h2 : Continuous fun p : ℝ × ℂ => circleMap z r p.1 - (x - p.2) :=
    ((continuous_circleMap z r).comp continuous_fst).sub (continuous_const.sub continuous_snd)
  exact (h1.comp continuous_snd).measurable.mul (Real.measurable_log.comp h2.measurable.norm).neg

lemma integrable_fubF : Integrable (fubF k z r x) (μθ.prod volume) := by
  obtain ⟨M, hM⟩ := (bumpTest k 0).continuous.bounded_above_of_compact_support
    (bumpTest k 0).hasCompactSupport
  set B := closedBall z (|r| + 1)
  set b : ℂ → ℝ := fun y => M * (B.indicator (fun y => ‖x - y‖) y + logBallFun (x - y))
  have hb : Integrable b := by
    refine Integrable.const_mul (Integrable.add ?_ (integrable_logBallFun.comp_sub_left x)) M
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact (continuous_const.sub continuous_id).norm.continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)
  refine Integrable.mono' (hb.comp_snd μθ) (measurable_fubF k z r x).aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  simp only [fubF, b, norm_mul, norm_neg]
  by_cases hp : ‖p.2 - circleMap z r p.1‖ < 1
  · have hpB : p.2 ∈ B := by
      have h2 : dist (circleMap z r p.1) z = |r| := by
        simp [dist_eq_norm, circleMap_sub_center]
      have h3 : dist p.2 (circleMap z r p.1) < 1 := by rw [dist_eq_norm]; exact hp
      rw [mem_closedBall]
      linarith [dist_triangle p.2 (circleMap z r p.1) z]
    rw [indicator_of_mem hpB, mul_comm]
    refine mul_le_mul (hM _) ?_ (norm_nonneg _) hM0
    rw [Real.norm_eq_abs]
    exact abs_log_norm_le (x - p.2)
  · rw [bumpTest_eq_zero k (by rw [dist_zero_right]; linarith), norm_zero, mul_zero]
    have : 0 ≤ B.indicator (fun y => ‖x - y‖) p.2 + logBallFun (x - p.2) :=
      add_nonneg (indicator_nonneg (fun _ _ => norm_nonneg _) _) (logBallFun_nonneg _)
    positivity

lemma integrable_fubG : Integrable (fubG k z r x) (μθ.prod volume) := by
  have hF := integrable_fubF k z r x
  rw [integrable_prod_iff (measurable_fubG k z r x).aestronglyMeasurable]
  constructor
  · filter_upwards [hF.prod_right_ae] with θ hθ
    have := hθ.comp_add_right (circleMap z r θ)
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [fubG_eq]
  · refine hF.integral_norm_prod_left.congr (Eventually.of_forall fun θ => ?_)
    simp only
    rw [← integral_add_right_eq_self (fun y => ‖fubF k z r x (θ, y)‖) (circleMap z r θ)]
    simp only [fubG_eq]

/-- **The log potential of `circBump`:** `logPot Φ_k x = −∫ ψ_k(t) g_{z,r}(x − t) dt`. -/
theorem logPot_circBump :
    logPot (circBump k z r) x = -∫ t, bumpTest k 0 t * circLog z r (x - t) := by
  have e1 : logPot (circBump k z r) x =
      (2 * π)⁻¹ * ∫ y, ∫ θ, fubF k z r x (θ, y) ∂μθ := by
    rw [logPot, ← integral_const_mul]
    congr 1
    funext y
    rw [circBump_eq_integral, mul_left_comm, ← integral_const_mul]
    rfl
  have e2 : ∫ y, ∫ θ, fubF k z r x (θ, y) ∂μθ = ∫ θ, (∫ t, fubG k z r x (θ, t)) ∂μθ := by
    rw [← integral_integral_swap (f := fun θ y => fubF k z r x (θ, y))
      (integrable_fubF k z r x)]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only
    rw [← integral_add_right_eq_self (fun y => fubF k z r x (θ, y)) (circleMap z r θ)]
    simp only [fubG_eq]
  have e3 : ∫ θ, (∫ t, fubG k z r x (θ, t)) ∂μθ = ∫ t, ∫ θ, fubG k z r x (θ, t) ∂μθ :=
    integral_integral_swap (f := fun θ t => fubG k z r x (θ, t)) (integrable_fubG k z r x)
  rw [e1, e2, e3, ← integral_const_mul, ← integral_neg]
  congr 1
  funext t
  simp only [fubG, circLog, Real.circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  rw [integral_const_mul, integral_neg]
  ring

end Fubini

end CircleAvg
end LQGMetric
