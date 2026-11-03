/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.CircleAvgCont at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGauss
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# `circleAvg` of a continuous function is its classical circle average

For `f : C(ℂ, ℝ)`, `circleAvg (ofCont f) r z = Real.circleAverage f z r` (`circleAvg_ofCont`), as
claimed in FOUNDATIONS §3 ("for continuous `h = ofCont f` both definitions return the classical
circle average"). Consequently, for `h − f` a field whose circle average exists,
`circleAvg (h) r z = circleAvg (h − ofCont f) r z + Real.circleAverage f z r`
(`circleAvg_add_ofCont_of_tendsto`), which reduces circle averages of `IsGFFPlusCont` fields to
those of the GFF part.

Proof: `⟨ofCont f, ψ_{n,x}⟩ = (ψ_n ⋆ f)(x) → f(x)` (mathlib
`ContDiffBump.convolution_tendsto_right_of_continuous`), dominated by `sup |f|` over a
neighbourhood of the circle, and dominated convergence for the circle average.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped Convolution

namespace LQGMetric
namespace CircleAvg

lemma bumpTest_comm (n : ℕ) (x y : ℂ) : bumpTest n x y = (bumpAt n 0).normed volume (x - y) := by
  rw [bumpTest_eq_sub, bumpTest_apply, ← ContDiffBump.normed_neg, neg_sub]

/-- `⟨f, ψ_{n,x}⟩ = (ψ_n ⋆ f)(x)` -/
lemma ofCont_bumpTest (f : C(ℂ, ℝ)) (n : ℕ) (x : ℂ) :
    ofCont f (bumpTest n x) =
      ((bumpAt n 0).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (f : ℂ → ℝ)) x := by
  rw [ofCont_apply, convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_sub_left_eq_self (fun t => (bumpAt n 0).normed volume t * f (x - t)) volume x]
  congr 1
  funext y
  simp only [sub_sub_cancel, bumpTest_comm]

lemma tendsto_ofCont_bumpTest (f : C(ℂ, ℝ)) (x : ℂ) :
    Tendsto (fun n => ofCont f (bumpTest n x)) atTop (𝓝 (f x)) := by
  simp_rw [ofCont_bumpTest]
  refine ContDiffBump.convolution_tendsto_right_of_continuous ?_ f.continuous x
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

lemma abs_ofCont_bumpTest_le (f : C(ℂ, ℝ)) (n : ℕ) {x : ℂ} {M : ℝ}
    (hM : ∀ y ∈ closedBall x 1, |f y| ≤ M) : |ofCont f (bumpTest n x)| ≤ M := by
  rw [ofCont_apply]
  have hb : ∀ y, ‖bumpTest n x y * f y‖ ≤ bumpTest n x y * M := by
    intro y
    have h0 : 0 ≤ bumpTest n x y := (bumpAt n x).nonneg_normed y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    by_cases hy : y ∈ closedBall x 1
    · exact mul_le_mul_of_nonneg_left (hM y hy) h0
    · rw [bumpTest_eq_zero n (le_of_lt (by simpa using hy)), zero_mul, zero_mul]
  have h1 := norm_integral_le_of_norm_le ((integrable_testC (bumpTest n x)).mul_const M)
    (Eventually.of_forall hb)
  rwa [integral_mul_const, integral_bumpTest', one_mul, Real.norm_eq_abs] at h1

/-- the mollified circle averages of a continuous function converge to its circle average -/
theorem tendsto_mollAvg_ofCont (f : C(ℂ, ℝ)) (r : ℝ) (z : ℂ) :
    Tendsto (fun n => mollAvg (ofCont f) n z r) atTop (𝓝 (Real.circleAverage f z r)) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall z (|r| + 1)).exists_bound_of_continuousOn
    f.continuous.continuousOn
  have hM' : ∀ θ, ∀ y ∈ closedBall (circleMap z r θ) 1, |f y| ≤ M := by
    intro θ y hy
    have := hM y ?_
    · simpa [Real.norm_eq_abs] using this
    rw [mem_closedBall] at hy ⊢
    have h2 : dist (circleMap z r θ) z = |r| := by simp [dist_eq_norm, circleMap_sub_center]
    linarith [dist_triangle y (circleMap z r θ) z]
  simp only [mollAvg, Real.circleAverage_def]
  refine Tendsto.const_smul ?_ _
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M) ?_ ?_
    intervalIntegrable_const ?_
  · refine Eventually.of_forall fun n => ?_
    have := (circleIntegrable_pairing (ofCont f) n z r)
    exact this.def'.aestronglyMeasurable
  · exact Eventually.of_forall fun n => Eventually.of_forall fun θ _ => by
      rw [Real.norm_eq_abs]; exact abs_ofCont_bumpTest_le f n (hM' θ)
  · exact Eventually.of_forall fun θ _ => tendsto_ofCont_bumpTest f _

/-- For `g = (g − f) + f` with `f` continuous: wherever the defining limit for `g − f` exists,
`g_r(z) = (g − f)_r(z) + (classical circle average of f)`; and the limit for `g` exists too. -/
theorem circleAvg_eq_sub_ofCont_add {g : DistC} {f : C(ℂ, ℝ)} {r : ℝ} {z : ℂ} {a : ℝ}
    (ha : Tendsto (fun n => mollAvg (g - ofCont f) n z r) atTop (𝓝 a)) :
    Tendsto (fun n => mollAvg g n z r) atTop (𝓝 (a + Real.circleAverage f z r)) ∧
      circleAvg g r z = circleAvg (g - ofCont f) r z + Real.circleAverage f z r := by
  have hsplit : ∀ n, mollAvg g n z r = mollAvg (g - ofCont f) n z r + mollAvg (ofCont f) n z r := by
    intro n
    simp only [mollAvg_eq, sub_apply, sub_add_cancel]
  have ht : Tendsto (fun n => mollAvg g n z r) atTop (𝓝 (a + Real.circleAverage f z r)) := by
    simp_rw [hsplit]
    exact ha.add (tendsto_mollAvg_ofCont f r z)
  exact ⟨ht, by rw [circleAvg_eq_of_tendsto ht, circleAvg_eq_of_tendsto ha]⟩

end CircleAvg
end LQGMetric
