/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.PathSpaceDUnif

/-!
# Time dilation and scalar multiplication of continuous paths in the local uniform metric

For `X : C(ℝ≥0, E)` let `timeScalePath c X = (t ↦ X (c * t))`.

* `LatticeProb.dUnif_timeScalePath_le`: if `c ≤ 1` then
  `dUnif (timeScalePath c X) (timeScalePath c Y) ≤ dUnif X Y`
  (the supremum over `[0, T]` after dilation is a supremum over `[0, c T] ⊆ [0, T]`);
  `lipschitzWith_timeScalePath` is the `1`-Lipschitz statement for the local uniform metric.
* `LatticeProb.dUnif_smul_le`: for paths in a normed space and `c ≥ 1`,
  `dUnif (c • X) (c • Y) ≤ c * dUnif X Y`; `lipschitzWith_smulPath` is the `c`-Lipschitz statement.
-/

open Filter Topology Set MeasureTheory Metric

open scoped NNReal

noncomputable section

namespace LatticeProb

section TimeScale

variable {E : Type*} [MetricSpace E]

/-- The time dilation `X ↦ (t ↦ X (c * t))` of a continuous path. -/
def timeScalePath (c : ℝ≥0) (X : C(ℝ≥0, E)) : C(ℝ≥0, E) :=
  X.comp ⟨fun t => c * t, continuous_const.mul continuous_id⟩

@[simp] lemma timeScalePath_apply (c : ℝ≥0) (X : C(ℝ≥0, E)) (t : ℝ≥0) :
    timeScalePath c X t = X (c * t) := rfl

lemma pathSupDist_timeScalePath_le {c : ℝ≥0} (hc : c ≤ 1) (T : ℝ≥0) (X Y : C(ℝ≥0, E)) :
    pathSupDist T (timeScalePath c X) (timeScalePath c Y) ≤ pathSupDist T X Y :=
  pathSupDist_le fun _ ht =>
    dist_le_pathSupDist X Y ((mul_le_of_le_one_left zero_le hc).trans ht)

/-- **Time dilation by `c ≤ 1` does not increase the local uniform distance.** -/
theorem dUnif_timeScalePath_le {c : ℝ≥0} (hc : c ≤ 1) (X Y : C(ℝ≥0, E)) :
    dUnif (timeScalePath c X) (timeScalePath c Y) ≤ dUnif X Y := by
  unfold dUnif
  refine integral_mono_of_nonneg (ae_of_all _ fun _ => dUnifIntegrand_nonneg)
    (integrableOn_dUnifIntegrand X Y) (ae_of_all _ fun T => ?_)
  exact min_le_min le_rfl (pathSupDist_timeScalePath_le hc _ X Y)

attribute [local instance] dUnifMetricSpace in
/-- The time dilation by `c ≤ 1` is `1`-Lipschitz for the local uniform metric. -/
theorem lipschitzWith_timeScalePath {c : ℝ≥0} (hc : c ≤ 1) :
    LipschitzWith 1 (timeScalePath c : C(ℝ≥0, E) → C(ℝ≥0, E)) :=
  LipschitzWith.of_dist_le_mul fun X Y => by
    rw [NNReal.coe_one, one_mul]
    exact dUnif_timeScalePath_le hc X Y

end TimeScale

section Smul

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma pathSupDist_smul_le {c : ℝ} (hc : 0 ≤ c) (T : ℝ≥0) (X Y : C(ℝ≥0, F)) :
    pathSupDist T (c • X) (c • Y) ≤ c * pathSupDist T X Y :=
  pathSupDist_le fun t ht => by
    simp only [ContinuousMap.smul_apply]
    rw [dist_smul₀, Real.norm_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (dist_le_pathSupDist X Y ht) hc

/-- **Multiplying paths by `c ≥ 1` multiplies the local uniform distance by at most `c`.** -/
theorem dUnif_smul_le {c : ℝ} (hc : 1 ≤ c) (X Y : C(ℝ≥0, F)) :
    dUnif (c • X) (c • Y) ≤ c * dUnif X Y := by
  unfold dUnif
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun _ => dUnifIntegrand_nonneg)
    ((integrableOn_dUnifIntegrand X Y).const_mul c) (ae_of_all _ fun T => ?_)
  beta_reduce
  unfold dUnifIntegrand
  rcases le_total (pathSupDist T.toNNReal X Y) (Real.exp (-T)) with h | h
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans (pathSupDist_smul_le (by linarith) _ X Y)
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (le_mul_of_one_le_left (Real.exp_pos _).le hc)

attribute [local instance] dUnifMetricSpace in
/-- Multiplication of paths by `c ≥ 1` is `c`-Lipschitz for the local uniform metric. -/
theorem lipschitzWith_smulPath {c : ℝ≥0} (hc : 1 ≤ c) :
    LipschitzWith c (fun X : C(ℝ≥0, F) => (c : ℝ) • X) :=
  LipschitzWith.of_dist_le_mul fun X Y =>
    dUnif_smul_le (by exact_mod_cast hc) X Y

end Smul

end LatticeProb
