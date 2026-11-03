/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.StandardBorelMetric at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.Metric
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The space of continuous metrics is standard Borel (FOUNDATIONS §9 item 4, second half)

`C(ℂ × ℂ, ℝ)` (compact-open topology, Borel σ-algebra) is Polish (mathlib instances; see
`LQGMetric/Prob/PolishContinuousMap.lean`), hence standard Borel. The set of continuous metrics
`{d | IsContinuousMetric d}` is Borel: it is
`A ∩ ⋂_{R, m ∈ ℕ} ⋃_{k ∈ ℕ} B_{R,m,k}` with `A` (zero diagonal, symmetry, triangle inequality)
closed and `B_{R,m,k} = {d | ∀ x ∈ B̄_R(0), ∀ y, 1/(m+1) ≤ |y - x| → 1/(k+1) ≤ d(x,y)}` closed
(`isContinuousMetric_iff`; the forward direction is a compactness argument on `B̄_R(0)`).
So `ContMetric` is standard Borel (mathlib `MeasurableSet.standardBorel`).

Own elementary argument (no specific published source for this exact characterization).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace LQGMetric

/-- the closed algebraic part of "continuous metric" -/
def metricAlgSet : Set C(ℂ × ℂ, ℝ) :=
  {d | (∀ x, d (x, x) = 0) ∧ (∀ x y, d (x, y) = d (y, x)) ∧
    ∀ x y z, d (x, z) ≤ d (x, y) + d (y, z)}

/-- the uniform separation condition on `B̄_R(0)` -/
def metricSepSet (R m k : ℕ) : Set C(ℂ × ℂ, ℝ) :=
  {d | ∀ x ∈ closedBall (0 : ℂ) R, ∀ y : ℂ, 1 / ((m : ℝ) + 1) ≤ ‖y - x‖ →
    1 / ((k : ℝ) + 1) ≤ d (x, y)}

theorem isClosed_metricAlgSet : IsClosed metricAlgSet := by
  have h1 : IsClosed {d : C(ℂ × ℂ, ℝ) | ∀ x, d (x, x) = 0} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x => isClosed_eq (continuous_eval_const _) continuous_const
  have h2 : IsClosed {d : C(ℂ × ℂ, ℝ) | ∀ x y, d (x, y) = d (y, x)} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_eval_const _) (continuous_eval_const _)
  have h3 : IsClosed {d : C(ℂ × ℂ, ℝ) | ∀ x y z, d (x, z) ≤ d (x, y) + d (y, z)} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z =>
      isClosed_le (continuous_eval_const _)
        ((continuous_eval_const _).add (continuous_eval_const _))
  have : metricAlgSet = {d : C(ℂ × ℂ, ℝ) | ∀ x, d (x, x) = 0} ∩
      ({d | ∀ x y, d (x, y) = d (y, x)} ∩ {d | ∀ x y z, d (x, z) ≤ d (x, y) + d (y, z)}) := by
    ext d; rfl
  rw [this]
  exact h1.inter (h2.inter h3)

theorem isClosed_metricSepSet (R m k : ℕ) : IsClosed (metricSepSet R m k) := by
  unfold metricSepSet
  simp only [ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_iInter fun y =>
    isClosed_iInter fun _ => isClosed_le continuous_const (continuous_eval_const _)

/-- forward direction: a continuous metric is uniformly separated on bounded sets -/
theorem exists_sep_of_isContinuousMetric {d : C(ℂ × ℂ, ℝ)} (hd : IsContinuousMetric d)
    (R m : ℕ) : ∃ k : ℕ, d ∈ metricSepSet R m k := by
  by_contra hne
  push Not at hne
  have hne' : ∀ k : ℕ, ∃ x ∈ closedBall (0 : ℂ) R, ∃ y : ℂ,
      1 / ((m : ℝ) + 1) ≤ ‖y - x‖ ∧ d (x, y) < 1 / ((k : ℝ) + 1) := by
    intro k
    have := hne k
    simp only [metricSepSet, mem_ofPred_eq, not_forall, not_le, exists_prop] at this
    exact this
  choose x hx y hy using hne'
  obtain ⟨xs, hxs, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : ℂ) R).tendsto_subseq hx
  set ε : ℝ := 1 / (2 * ((m : ℝ) + 1)) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨δ, hδ, hsmall⟩ := hd.euclidean_of_small xs ε hεpos
  -- `d(xs, x_{φ k}) → 0`
  have h1 : Tendsto (fun k => d (xs, x (φ k))) atTop (𝓝 0) := by
    have := (d.continuous.tendsto (xs, xs)).comp (tendsto_const_nhds.prodMk_nhds hlim)
    rwa [Function.comp_def, hd.self_eq_zero xs] at this
  have h2 : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have e1 := (tendsto_order.1 h1).2 (δ / 2) (half_pos hδ)
  have e2 := (tendsto_order.1 h2).2 (δ / 2) (half_pos hδ)
  have e3 := (Metric.tendsto_nhds.1 hlim) ε hεpos
  obtain ⟨k, hk1, hk2, hk3⟩ := (e1.and (e2.and e3)).exists
  have hdy : d (xs, y (φ k)) < δ := by
    have := hd.triangle xs (x (φ k)) (y (φ k))
    linarith [(hy (φ k)).2]
  have hn1 : ‖xs - y (φ k)‖ < ε := hsmall _ hdy
  have hn2 : ‖x (φ k) - xs‖ < ε := by rw [← dist_eq_norm]; exact hk3
  have hn3 : ‖y (φ k) - x (φ k)‖ ≤ ‖xs - y (φ k)‖ + ‖x (φ k) - xs‖ := by
    calc ‖y (φ k) - x (φ k)‖ = ‖-(xs - y (φ k)) + -(x (φ k) - xs)‖ := by congr 1; ring
      _ ≤ ‖-(xs - y (φ k))‖ + ‖-(x (φ k) - xs)‖ := norm_add_le _ _
      _ = _ := by rw [norm_neg, norm_neg]
  have : 1 / ((m : ℝ) + 1) = 2 * ε := by rw [hε]; field_simp
  linarith [(hy (φ k)).1]

/-- characterization of continuous metrics by closed and `F_σ` conditions -/
theorem isContinuousMetric_iff (d : C(ℂ × ℂ, ℝ)) :
    IsContinuousMetric d ↔ d ∈ metricAlgSet ∧ ∀ R m : ℕ, ∃ k : ℕ, d ∈ metricSepSet R m k := by
  refine ⟨fun hd => ⟨⟨hd.self_eq_zero, hd.symm, hd.triangle⟩,
    exists_sep_of_isContinuousMetric hd⟩, fun ⟨hA, hB⟩ => ?_⟩
  have key : ∀ x y : ℂ, 0 < ‖y - x‖ → ∃ δ > 0, ∀ y' : ℂ, ‖y - x‖ ≤ ‖y' - x‖ → δ ≤ d (x, y') := by
    intro x y hxy
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hxy
    obtain ⟨k, hk⟩ := hB (⌈‖x‖⌉₊) m
    refine ⟨1 / ((k : ℝ) + 1), by positivity, fun y' hy' => hk x ?_ y' (by linarith)⟩
    rw [mem_closedBall, dist_zero_right]
    exact Nat.le_ceil _
  refine ⟨⟨hA.1, fun x y hxy => ?_, hA.2.1, hA.2.2⟩, fun x ε hε => ?_⟩
  · by_contra hne
    have hpos : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne))
    obtain ⟨δ, hδ, h⟩ := key x y hpos
    linarith [h y le_rfl]
  · obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨k, hk⟩ := hB (⌈‖x‖⌉₊) m
    refine ⟨1 / ((k : ℝ) + 1), by positivity, fun y hy => ?_⟩
    by_contra hne
    push Not at hne
    have hx : x ∈ closedBall (0 : ℂ) (⌈‖x‖⌉₊ : ℕ) := by
      rw [mem_closedBall, dist_zero_right]; exact Nat.le_ceil _
    have := hk x hx y (by rw [norm_sub_rev]; linarith)
    linarith

theorem measurableSet_isContinuousMetric :
    MeasurableSet {d : C(ℂ × ℂ, ℝ) | IsContinuousMetric d} := by
  have : {d : C(ℂ × ℂ, ℝ) | IsContinuousMetric d} =
      metricAlgSet ∩ ⋂ R : ℕ, ⋂ m : ℕ, ⋃ k : ℕ, metricSepSet R m k := by
    ext d
    simp only [mem_ofPred_eq, isContinuousMetric_iff, mem_inter_iff, mem_iInter, mem_iUnion]
  rw [this]
  exact isClosed_metricAlgSet.measurableSet.inter (MeasurableSet.iInter fun R =>
    MeasurableSet.iInter fun m => MeasurableSet.iUnion fun k =>
      (isClosed_metricSepSet R m k).measurableSet)

/-- the space `ContMetric` of continuous metrics on `ℂ` is standard Borel -/
instance standardBorelSpace_contMetric : StandardBorelSpace ContMetric :=
  measurableSet_isContinuousMetric.standardBorel

end LQGMetric
