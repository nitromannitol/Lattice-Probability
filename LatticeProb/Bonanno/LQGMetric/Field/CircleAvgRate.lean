/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.CircleAvgRate at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgVar

/-!
# Rate for the mollified circle averages; a.s. existence of `h_r(z)`

`logCov_circDiff_succ_le`: for `r > 0`, the increment `D = circBump (n+1) z r − circBump n z r`
satisfies `logCov D D ≤ (4/r) (1/2)ⁿ`. Proof (own elementary argument, see `CircleAvgVar`):
`logPot Φ_k x = −∫ ψ_k(t) g(x − t) dt` with `g` `1/r`-Lipschitz and `ψ_k` a probability density
supported in `B(0, 2^{-k})`, so `|logPot D| ≤ (2^{-n-1} + 2^{-n})/r`, and
`logCov D D = ∫ D · logPot D ≤ ‖D‖₁ sup |logPot D| ≤ 2 (2^{-n-1} + 2^{-n})/r`.

Main results: for a whole-plane GFF `h` and `r > 0`, almost surely the limit defining
`circleAvg (h ω) r z` exists (`ae_tendsto_mollAvg`), and almost surely
`(h + c)_r(z) = h_r(z) + c` for all `c` (`ae_circleAvg_addConst`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped Real

namespace LQGMetric
namespace CircleAvg

lemma bumpTest_eq_zero_of_le (n : ℕ) {x y : ℂ} (hy : (2 : ℝ)⁻¹ ^ n ≤ dist y x) :
    bumpTest n x y = 0 := by
  rw [bumpTest_apply, ContDiffBump.normed_def, (bumpAt n x).zero_of_le_dist hy, zero_div]

lemma bumpTest_nonneg (n : ℕ) (x y : ℂ) : 0 ≤ bumpTest n x y := (bumpAt n x).nonneg_normed y

lemma circBump_nonneg (n : ℕ) (z : ℂ) (r : ℝ) (y : ℂ) : 0 ≤ circBump n z r y := by
  rw [circBump_apply]
  exact Real.circleAverage_nonneg_of_nonneg fun x _ => bumpTest_nonneg n x y

lemma continuous_circLog {r : ℝ} (hr : r ≠ 0) (z : ℂ) : Continuous (circLog z r) := by
  have : circLog z r = fun u => Real.log r + Real.posLog (r⁻¹ * ‖z - u‖) :=
    funext fun u => circLog_eq hr z u
  rw [this]
  fun_prop

/-- `−log|x − ·| φ` is integrable for a test function `φ` -/
lemma integrable_log_mul_test (φ : TestC) (x : ℂ) :
    Integrable fun y => -Real.log ‖x - y‖ * φ y := by
  obtain ⟨M, hM⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  set B := closedBall (0 : ℂ) R
  set b : ℂ → ℝ := fun y => M * (B.indicator (fun y => ‖x - y‖) y + logBallFun (x - y))
  have hb : Integrable b := by
    refine Integrable.const_mul (Integrable.add ?_ (integrable_logBallFun.comp_sub_left x)) M
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact (continuous_const.sub continuous_id).norm.continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)
  have hmeas : Measurable fun y => -Real.log ‖x - y‖ * φ y :=
    ((Real.measurable_log.comp (measurable_const.sub measurable_id).norm).neg).mul
      φ.continuous.measurable
  refine Integrable.mono' hb hmeas.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  simp only [b, norm_mul, norm_neg]
  by_cases hy : y ∈ tsupport φ
  · rw [indicator_of_mem (hR hy), mul_comm]
    refine mul_le_mul (hM _) ?_ (norm_nonneg _) hM0
    rw [Real.norm_eq_abs]
    exact abs_log_norm_le (x - y)
  · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero, mul_zero]
    have : 0 ≤ B.indicator (fun y => ‖x - y‖) y + logBallFun (x - y) :=
      add_nonneg (indicator_nonneg (fun _ _ => norm_nonneg _) _) (logBallFun_nonneg _)
    positivity

lemma logPot_sub (φ ψ : TestC) (x : ℂ) :
    logPot (⇑(φ - ψ)) x = logPot φ x - logPot ψ x := by
  unfold logPot
  rw [← integral_sub (integrable_log_mul_test φ x) (integrable_log_mul_test ψ x)]
  congr 1
  funext y
  simp only [FunLike.coe_sub, Pi.sub_apply]
  ring

/-- `|∫ ψ_k(t) g(x − t) dt − g(x)| ≤ 2^{-k}/r` -/
lemma abs_integral_bump_circLog_sub_le {r : ℝ} (hr : 0 < r) (k : ℕ) (z x : ℂ) :
    |(∫ t, bumpTest k 0 t * circLog z r (x - t)) - circLog z r x| ≤ (2 : ℝ)⁻¹ ^ k / r := by
  have hgc : Continuous fun t => circLog z r (x - t) :=
    (continuous_circLog hr.ne' z).comp (continuous_const.sub continuous_id)
  have hi1 : Integrable fun t => bumpTest k 0 t * circLog z r (x - t) :=
    ((bumpTest k 0).continuous.mul hgc).integrable_of_hasCompactSupport
      ((bumpTest k 0).hasCompactSupport.mul_right)
  have hi2 : Integrable fun t => bumpTest k 0 t * circLog z r x :=
    (integrable_testC _).mul_const _
  have e : (∫ t, bumpTest k 0 t * circLog z r (x - t)) - circLog z r x =
      ∫ t, bumpTest k 0 t * (circLog z r (x - t) - circLog z r x) := by
    simp_rw [mul_sub]
    rw [integral_sub hi1 hi2, integral_mul_const, integral_bumpTest', one_mul]
  rw [e, ← Real.norm_eq_abs]
  have hb : ∀ t, ‖bumpTest k 0 t * (circLog z r (x - t) - circLog z r x)‖ ≤
      bumpTest k 0 t * ((2 : ℝ)⁻¹ ^ k / r) := by
    intro t
    rw [norm_mul, Real.norm_of_nonneg (bumpTest_nonneg k 0 t)]
    by_cases ht : ‖t‖ < (2 : ℝ)⁻¹ ^ k
    · refine mul_le_mul_of_nonneg_left ?_ (bumpTest_nonneg k 0 t)
      rw [Real.norm_eq_abs]
      refine (abs_circLog_sub_le hr z _ _).trans ?_
      rw [sub_sub_cancel_left, norm_neg]
      gcongr
    · rw [bumpTest_eq_zero_of_le k (by rw [dist_zero_right]; linarith), zero_mul, zero_mul]
  refine (norm_integral_le_of_norm_le ((integrable_testC _).mul_const _)
    (Eventually.of_forall hb)).trans (le_of_eq ?_)
  rw [integral_mul_const, integral_bumpTest', one_mul]

lemma abs_logPot_circDiff_le {r : ℝ} (hr : 0 < r) (n : ℕ) (z x : ℂ) :
    |logPot (circDiff (n + 1) z r n z r).1 x| ≤ 2 * (2 : ℝ)⁻¹ ^ n / r := by
  show |logPot (⇑(circBump (n + 1) z r - circBump n z r)) x| ≤ _
  rw [logPot_sub, logPot_circBump, logPot_circBump]
  have h1 := abs_integral_bump_circLog_sub_le hr (n + 1) z x
  have h2 := abs_integral_bump_circLog_sub_le hr n z x
  have h3 : (2 : ℝ)⁻¹ ^ (n + 1) / r ≤ (2 : ℝ)⁻¹ ^ n / r := by
    have : (2 : ℝ)⁻¹ ^ (n + 1) ≤ (2 : ℝ)⁻¹ ^ n := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (by positivity) (by norm_num)
    exact div_le_div_of_nonneg_right this hr.le
  have h4 : 2 * (2 : ℝ)⁻¹ ^ n / r = (2 : ℝ)⁻¹ ^ n / r + (2 : ℝ)⁻¹ ^ n / r := by ring
  rw [abs_le] at h1 h2 ⊢
  rw [h4]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Variance rate.** `Var(h_{n+1} − h_n) = logCov D D ≤ (4/r) (1/2)ⁿ` for the mollified circle
averages at a fixed circle `∂B(z, r)`, `r > 0`. -/
theorem logCov_circDiff_succ_le {r : ℝ} (hr : 0 < r) (z : ℂ) (n : ℕ) :
    logCov (circDiff (n + 1) z r n z r).1 (circDiff (n + 1) z r n z r).1 ≤
      4 / r * (2 : ℝ)⁻¹ ^ n := by
  set D := circDiff (n + 1) z r n z r
  set c := 2 * (2 : ℝ)⁻¹ ^ n / r
  rw [logCov_eq_integral_logPot]
  have hD : ∀ x, |D.1 x| ≤ circBump (n + 1) z r x + circBump n z r x := by
    intro x
    show |circBump (n + 1) z r x - circBump n z r x| ≤ _
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_of_nonneg (circBump_nonneg _ _ _ _), abs_of_nonneg (circBump_nonneg _ _ _ _)]
  have hb : ∀ x, ‖D.1 x * logPot D.1 x‖ ≤ (circBump (n + 1) z r x + circBump n z r x) * c := by
    intro x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (hD x) (abs_logPot_circDiff_le hr n z x) (abs_nonneg _)
      (add_nonneg (circBump_nonneg _ _ _ _) (circBump_nonneg _ _ _ _))
  have hint : Integrable fun x => (circBump (n + 1) z r x + circBump n z r x) * c :=
    ((integrable_testC _).add (integrable_testC _)).mul_const c
  have := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans
    (norm_integral_le_of_norm_le hint (Eventually.of_forall hb)))
  refine this.trans (le_of_eq ?_)
  rw [integral_mul_const, integral_add (integrable_testC _) (integrable_testC _),
    integral_circBump, integral_circBump]
  simp only [c]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- **The circle average exists a.s.** For a whole-plane GFF and `r > 0`, almost surely the
mollified circle averages converge, i.e. the limit defining `circleAvg (h ω) r z` exists. -/
theorem ae_tendsto_mollAvg (hh : IsWholePlaneGFF h P) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∃ a, Tendsto (fun n => mollAvg (h ω) n z r) atTop (𝓝 a) :=
  ae_tendsto_mollAvg_of_logCov_le hh z r (C := 4 / r) (q := 2⁻¹) (by norm_num) (by norm_num)
    (logCov_circDiff_succ_le hr z)

/-- `(h + c)_r(z) = h_r(z) + c` for all `c`, almost surely. -/
theorem ae_circleAvg_addConst (hh : IsWholePlaneGFF h P) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ c, circleAvg (addConst (h ω) c) r z = circleAvg (h ω) r z + c :=
  ae_circleAvg_addConst_of_logCov_le hh z r (C := 4 / r) (q := 2⁻¹) (by norm_num) (by norm_num)
    (logCov_circDiff_succ_le hr z)

/-- P2-FINV leaf (a): the unit circle around `0`. -/
theorem ae_circleAvg_addConst_one_zero (hh : IsWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∀ c, circleAvg (addConst (h ω) c) 1 0 = circleAvg (h ω) 1 0 + c :=
  ae_circleAvg_addConst hh 0 one_pos

end CircleAvg
end LQGMetric
