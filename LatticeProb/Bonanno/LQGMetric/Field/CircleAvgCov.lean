/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.CircleAvgCov at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgAffine

/-!
# Limit of the covariances of the mollified circle-average increments

`circCov z r w s := ⨍_{∂B(z,r)} ⨍_{∂B(w,s)} log|a − b|` (`= ⨍_{∂B(z,r)} g_{w,s}`, with
`g_{w,s}(a) = log max(s, |w − a|)`). For radii `> 0`,
`logCov (circDiff n z r n w s) (circDiff n z' r' n w' s') → incCov …` where
`incCov = −C(zr, z'r') + C(zr, w's') + C(ws, z'r') − C(ws, w's')` (`tendsto_logCov_circDiff`):
the Duplantier–Sheffield covariance of circle averages (DS arXiv:0808.1560 §3.1: the covariance
of `h_ε(z)` and `h_δ(w)` is the double circle average of the Green function `−log|x − y|`).
Proof: `logCov D D' = ∫ D · logPot D'`, `logPot D'` is uniformly within `2^{-n}(1/r' + 1/s')`
of `−(g_{z',r'} − g_{w',s'})`, and `∫ D f = mollAvg (ofCont f)` differences, which converge to the
circle averages of `f` (`tendsto_mollAvg_ofCont`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped Real

namespace LQGMetric
namespace CircleAvg

/-- `⨍_{∂B(z,r)} ⨍_{∂B(w,s)} log|a − b|` -/
def circCov (z : ℂ) (r : ℝ) (w : ℂ) (s : ℝ) : ℝ := Real.circleAverage (circLog w s) z r

/-- the limit covariance of the increments `h_r(z) − h_s(w)` and `h_{r'}(z') − h_{s'}(w')` -/
def incCov (z : ℂ) (r : ℝ) (w : ℂ) (s : ℝ) (z' : ℂ) (r' : ℝ) (w' : ℂ) (s' : ℝ) : ℝ :=
  -circCov z r z' r' + circCov z r w' s' + circCov w s z' r' - circCov w s w' s'

/-- `g_{z',r'} − g_{w',s'}` as a continuous function -/
def circLogDiff {r' s' : ℝ} (hr' : r' ≠ 0) (hs' : s' ≠ 0) (z' w' : ℂ) : C(ℂ, ℝ) :=
  ⟨fun x => circLog z' r' x - circLog w' s' x,
    (continuous_circLog hr' z').sub (continuous_circLog hs' w')⟩

lemma integral_circBump_mul (f : C(ℂ, ℝ)) (n : ℕ) (z : ℂ) (r : ℝ) :
    ∫ x, circBump n z r x * f x = mollAvg (ofCont f) n z r := by
  rw [mollAvg_eq, ofCont_apply]

lemma integrable_test_mul (φ : TestC) (f : C(ℂ, ℝ)) : Integrable fun x => φ x * f x :=
  (φ.continuous.mul f.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right

lemma measurable_logPot (φ : TestC) : Measurable (logPot φ) := by
  have hm : Measurable fun p : ℂ × ℂ => -Real.log ‖p.1 - p.2‖ * φ p.2 :=
    ((Real.measurable_log.comp (measurable_fst.sub measurable_snd).norm).neg).mul
      (φ.continuous.measurable.comp measurable_snd)
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

lemma abs_logPot_circDiff_add_le {r' s' : ℝ} (hr' : 0 < r') (hs' : 0 < s') (n : ℕ)
    (z' w' x : ℂ) :
    |logPot (circDiff n z' r' n w' s').1 x + circLogDiff hr'.ne' hs'.ne' z' w' x| ≤
      (2 : ℝ)⁻¹ ^ n / r' + (2 : ℝ)⁻¹ ^ n / s' := by
  show |logPot (⇑(circBump n z' r' - circBump n w' s')) x +
    (circLog z' r' x - circLog w' s' x)| ≤ _
  rw [logPot_sub, logPot_circBump, logPot_circBump]
  have h1 := abs_integral_bump_circLog_sub_le hr' n z' x
  have h2 := abs_integral_bump_circLog_sub_le hs' n w' x
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Covariance limit** (DS §3.1). -/
theorem tendsto_logCov_circDiff {r s r' s' : ℝ} (hr : 0 < r) (hs : 0 < s) (hr' : 0 < r')
    (hs' : 0 < s') (z w z' w' : ℂ) :
    Tendsto (fun n => logCov (circDiff n z r n w s).1 (circDiff n z' r' n w' s').1) atTop
      (𝓝 (incCov z r w s z' r' w' s')) := by
  set f := circLogDiff hr'.ne' hs'.ne' z' w'
  set e : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ n / r' + (2 : ℝ)⁻¹ ^ n / s'
  -- decomposition
  have hdec : ∀ n, logCov (circDiff n z r n w s).1 (circDiff n z' r' n w' s').1 =
      -(mollAvg (ofCont f) n z r - mollAvg (ofCont f) n w s) +
        ∫ x, (circDiff n z r n w s).1 x *
          (logPot (circDiff n z' r' n w' s').1 x + f x) := by
    intro n
    set D := (circDiff n z r n w s).1
    set D' := (circDiff n z' r' n w' s').1
    have hDf : Integrable fun x => D x * f x := integrable_test_mul D f
    have hDe : Integrable fun x => D x * (logPot D' x + f x) := by
      refine Integrable.mono' ((integrable_testC D).norm.mul_const (e n))
        ((D.continuous.measurable.mul ((measurable_logPot D').add
          f.continuous.measurable)).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
      rw [norm_mul, Real.norm_eq_abs (_ + _)]
      exact mul_le_mul_of_nonneg_left (abs_logPot_circDiff_add_le hr' hs' n z' w' x)
        (norm_nonneg _)
    rw [logCov_eq_integral_logPot]
    have e1 : (fun x => D x * logPot D' x) =
        fun x => -(D x * f x) + D x * (logPot D' x + f x) := by funext x; ring
    rw [e1, integral_add (f := fun x => -(D x * f x)) hDf.neg hDe, integral_neg]
    congr 2
    show ∫ x, (circBump n z r x - circBump n w s x) * f x = _
    simp_rw [sub_mul]
    rw [integral_sub (integrable_test_mul _ f) (integrable_test_mul _ f),
      integral_circBump_mul, integral_circBump_mul]
  simp_rw [hdec]
  have hlim : incCov z r w s z' r' w' s' =
      -(Real.circleAverage f z r - Real.circleAverage f w s) + 0 := by
    have hci : ∀ (c : ℂ) (ρ : ℝ) (a : ℂ) (t : ℝ), t ≠ 0 →
        CircleIntegrable (circLog a t) c ρ := fun c ρ a t ht =>
      ((continuous_circLog ht a).continuousOn).circleIntegrable'
    show _ = -(Real.circleAverage (fun x => circLog z' r' x - circLog w' s' x) z r -
      Real.circleAverage (fun x => circLog z' r' x - circLog w' s' x) w s) + 0
    rw [Real.circleAverage_fun_sub (hci _ _ _ _ hr'.ne') (hci _ _ _ _ hs'.ne'),
      Real.circleAverage_fun_sub (hci _ _ _ _ hr'.ne') (hci _ _ _ _ hs'.ne')]
    simp only [incCov, circCov]
    ring
  rw [hlim]
  refine ((tendsto_mollAvg_ofCont f r z).sub (tendsto_mollAvg_ofCont f s w)).neg.add ?_
  have he : Tendsto (fun n => 2 * e n) atTop (𝓝 0) := by
    have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)
    have := ((h1.div_const r').add (h1.div_const s')).const_mul 2
    simpa [e] using this
  refine squeeze_zero_norm (fun n => ?_) he
  set D := (circDiff n z r n w s).1
  have hb : ∀ x, ‖D x * (logPot (circDiff n z' r' n w' s').1 x + f x)‖ ≤
      (circBump n z r x + circBump n w s x) * e n := by
    intro x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    refine mul_le_mul ?_ (abs_logPot_circDiff_add_le hr' hs' n z' w' x) (abs_nonneg _)
      (add_nonneg (circBump_nonneg _ _ _ _) (circBump_nonneg _ _ _ _))
    show |circBump n z r x - circBump n w s x| ≤ _
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_of_nonneg (circBump_nonneg _ _ _ _), abs_of_nonneg (circBump_nonneg _ _ _ _)]
  have hint : Integrable fun x => (circBump n z r x + circBump n w s x) * e n :=
    ((integrable_testC _).add (integrable_testC _)).mul_const _
  refine (norm_integral_le_of_norm_le hint (Eventually.of_forall hb)).trans (le_of_eq ?_)
  rw [integral_mul_const, integral_add (integrable_testC _) (integrable_testC _),
    integral_circBump, integral_circBump]
  ring

end CircleAvg
end LQGMetric
