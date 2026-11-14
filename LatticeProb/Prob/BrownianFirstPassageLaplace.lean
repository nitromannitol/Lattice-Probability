import LatticeProb.Prob.BrownianDriftExitMoment
import LatticeProb.Prob.BrownianFirstPassageStrict

/-!
# The Laplace transform of the Brownian first passage time

For a real Brownian motion `B` with continuous paths and a level `b > 0`, the first passage time
`T_b = inf {s | B s ≤ -b}` satisfies `E e^{-T_b} = e^{-√2 b}`. Optional stopping of the exponential martingale
`exp (-√2 B t - t)` at the bounded stopping times `T_b ∧ N` gives expectation `1`; up to `T_b` the martingale is at
most `e^{√2 b}`, and dominated convergence as `N → ∞` gives `E e^{√2 b - T_b} = 1`.

* `neg_le_of_le_hitDrift_neg`, `le_neg_of_hitDrift_neg_eq`: a continuous path started above `-b` stays at least
  `-b` up to its first passage time below `-b`, and is at most `-b` at that time;
* `integrable_and_integral_exp_hitDriftTrunc_neg`: optional stopping of the exponential martingale at `T_b ∧ N`;
* `integral_exp_neg_hitDrift_neg`: `E e^{-T_b} = e^{-√2 b}`;
* `integral_exp_neg_firstPassageBelow`: the same identity for the first passage time strictly below `B 0 - b` of
  the path extended to `ℝ`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace LatticeProb.LadderSet

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- Up to its first passage time below `-b`, a continuous path started above `-b` is at least `-b`. -/
theorem neg_le_of_le_hitDrift_neg (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ} {ω : Ω}
    (h0 : -b < B 0 ω) {s : ℝ≥0} (hs : (s : ℝ≥0∞) ≤ hitDrift (fun t ω => -B t ω) 0 b ω) :
    -b ≤ B s ω := by
  have hcont' : ∀ ω, Continuous fun s => (fun t ω => -B t ω) s ω := fun ω => (hcont ω).neg
  by_contra hlt
  have hlt' : B s ω < -b := not_le.1 hlt
  obtain ⟨r, hr, hBr⟩ := intermediate_value_Icc' (show (0 : ℝ≥0) ≤ s from zero_le) (hcont ω).continuousOn ⟨hlt'.le, h0.le⟩
  have hBr' : B r ω = -b := hBr
  have hrs : r < s := lt_of_le_of_ne hr.2 fun h => by rw [h] at hBr'; linarith
  have hle : hitDrift (fun t ω => -B t ω) 0 b ω ≤ (r : ℝ≥0∞) :=
    (hitDrift_le_iff hcont' 0 b ω r).2 ⟨r, le_rfl, by simp only [zero_mul, add_zero]; linarith⟩
  exact absurd (hle.trans_lt (by exact_mod_cast hrs)) (not_lt.2 hs)

omit [MeasurableSpace Ω] in
/-- At its first passage time below `-b`, when finite, a continuous path is at most `-b`. -/
theorem le_neg_of_hitDrift_neg_eq (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ} {ω : Ω} {t : ℝ≥0}
    (ht : hitDrift (fun t ω => -B t ω) 0 b ω = t) : B t ω ≤ -b := by
  have hcont' : ∀ ω, Continuous fun s => (fun t ω => -B t ω) s ω := fun ω => (hcont ω).neg
  obtain ⟨s, hst, hs⟩ := (hitDrift_le_iff hcont' 0 b ω t).1 ht.le
  have hs' : B s ω ≤ -b := by
    simp only [zero_mul, add_zero] at hs
    linarith
  rcases eq_or_lt_of_le hst with h | h
  · rw [← h]
    exact hs'
  · have hle : hitDrift (fun t ω => -B t ω) 0 b ω ≤ (s : ℝ≥0∞) :=
      (hitDrift_le_iff hcont' 0 b ω s).2 ⟨s, le_rfl, by simp only [zero_mul, add_zero]; linarith⟩
    rw [ht] at hle
    exact absurd (ENNReal.coe_le_coe.1 hle) (not_le.2 h)

/-- **Optional stopping of the exponential martingale at the truncated first passage time.** -/
theorem integrable_and_integral_exp_hitDriftTrunc_neg (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) (c b : ℝ) (N : ℝ≥0) :
    Integrable (fun ω => Real.exp (-(2 * c) * (B (hitDriftTrunc (fun t ω => -B t ω) 0 b N ω) ω +
      c * (hitDriftTrunc (fun t ω => -B t ω) 0 b N ω)))) P ∧
    ∫ ω, Real.exp (-(2 * c) * (B (hitDriftTrunc (fun t ω => -B t ω) 0 b N ω) ω +
      c * (hitDriftTrunc (fun t ω => -B t ω) 0 b N ω))) ∂P = 1 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hM := martingale_exp_drift hB hm c
  have hτ : IsStoppingTime (brownianFiltration B hm)
      fun ω => ((hitDriftTrunc (fun t ω => -B t ω) 0 b N ω : ℝ≥0) : ℝ≥0∞) := by
    have h := (isStoppingTime_hitDrift_neg_brownian hm hcont 0 b).min_const (i := N)
    rw [neg_zero] at h
    have hfun : (fun ω => ((hitDriftTrunc (fun t ω => -B t ω) 0 b N ω : ℝ≥0) : ℝ≥0∞)) =
        fun ω => min (hitDrift (fun t ω => -B t ω) 0 b ω) (N : ℝ≥0∞) := by
      funext ω
      exact coe_hitDriftTrunc _ _ _ _ _
    rw [hfun]
    exact h
  have hr : ∀ᵐ ω ∂P, ∀ t, ContinuousWithinAt
      (fun s : ℝ≥0 => Real.exp (-(2 * c) * (B s ω + c * s))) (Set.Ioi t) t :=
    Filter.Eventually.of_forall fun ω t =>
      (Real.continuous_exp.comp (continuous_const.mul ((hcont ω).add
        (continuous_const.mul NNReal.continuous_coe)))).continuousWithinAt
  have key := bounded_stopping_integrable_and_integral_eq_terminal hM hτ N
    (fun ω => by rw [coe_hitDriftTrunc]; exact inf_le_right) hr
  rw [integral_exp_drift hB c N] at key
  exact key

/-- **The Laplace transform of the Brownian first passage time.** For a real Brownian motion with continuous
paths and `b > 0`, the first passage time `T_b` below `-b` satisfies `E e^{-T_b} = e^{-√2 b}`. -/
theorem integral_exp_neg_hitDrift_neg [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ} (hb : 0 < b) :
    ∫ ω, Real.exp (-(hitDrift (fun t ω => -B t ω) 0 b ω).toReal) ∂P = Real.exp (-(√2 * b)) := by
  set c : ℝ := √2 / 2 with hc
  have hs2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2c : 2 * c = √2 := by
    rw [hc]
    ring
  have hcc : 2 * c * c = 1 := by
    rw [hc]
    linarith [hs2]
  have hc0 : 0 ≤ 2 * c := by
    rw [h2c]
    exact Real.sqrt_nonneg _
  have hc0' : 0 ≤ c := by linarith
  have hkey := fun N : ℕ =>
    integrable_and_integral_exp_hitDriftTrunc_neg hB.toIsPreBrownianReal hm hcont c b (N : ℝ≥0)
  have hB0 := hB.toIsPreBrownianReal.eval_zero_ae_eq_zero
  have hfin := ae_hitDrift_neg_lt_top hB hm hcont b
  have hbound : ∀ N : ℕ, ∀ᵐ ω ∂P,
      ‖Real.exp (-(2 * c) * (B (hitDriftTrunc (fun t ω => -B t ω) 0 b (N : ℝ≥0) ω) ω +
        c * (hitDriftTrunc (fun t ω => -B t ω) 0 b (N : ℝ≥0) ω)))‖ ≤ Real.exp (2 * c * b) := by
    intro N
    filter_upwards [hB0] with ω hω
    have h0 : -b < B 0 ω := by
      rw [hω]
      linarith
    have hle : ((hitDriftTrunc (fun t ω => -B t ω) 0 b (N : ℝ≥0) ω : ℝ≥0) : ℝ≥0∞) ≤
        hitDrift (fun t ω => -B t ω) 0 b ω := by
      rw [coe_hitDriftTrunc]
      exact inf_le_left
    have h1 := neg_le_of_le_hitDrift_neg hcont h0 hle
    have hτ0 := (hitDriftTrunc (fun t ω => -B t ω) 0 b (N : ℝ≥0) ω).coe_nonneg
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have h2 := mul_le_mul_of_nonneg_left
      (show -B (hitDriftTrunc (fun t ω => -B t ω) 0 b (N : ℝ≥0) ω) ω ≤ b by linarith) hc0
    have h3 := mul_nonneg (mul_nonneg hc0 hc0') hτ0
    linarith
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun N : ℕ =>
      Real.exp (-(2 * c) * (B (hitDriftTrunc (fun t ω => -B t ω) 0 b (N : ℝ≥0) ω) ω +
        c * (hitDriftTrunc (fun t ω => -B t ω) 0 b (N : ℝ≥0) ω)))) atTop
      (𝓝 (Real.exp (2 * c * b) * Real.exp (-(hitDrift (fun t ω => -B t ω) 0 b ω).toReal))) := by
    filter_upwards [hB0, hfin] with ω hω hfinω
    have h0 : -b < B 0 ω := by
      rw [hω]
      linarith
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hfinω.ne
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop n] with N hN
    have hTN : hitDrift (fun t ω => -B t ω) 0 b ω ≤ ((N : ℝ≥0) : ℝ≥0∞) := by
      refine hn.le.trans ?_
      rw [ENNReal.coe_natCast]
      exact_mod_cast hN
    have hco := coe_hitDriftTrunc_of_le (fun t ω => -B t ω) 0 b (N : ℝ≥0) ω hTN
    have hval : B (hitDriftTrunc (fun t ω => -B t ω) 0 b (N : ℝ≥0) ω) ω = -b :=
      le_antisymm (le_neg_of_hitDrift_neg_eq hcont hco.symm) (neg_le_of_le_hitDrift_neg hcont h0 hco.le)
    have hreal : (hitDrift (fun t ω => -B t ω) 0 b ω).toReal =
        (hitDriftTrunc (fun t ω => -B t ω) 0 b (N : ℝ≥0) ω : ℝ) := by
      rw [← hco, ENNReal.coe_toReal]
    have hmul : 2 * c * c * (hitDriftTrunc (fun t ω => -B t ω) 0 b (N : ℝ≥0) ω : ℝ) =
        hitDriftTrunc (fun t ω => -B t ω) 0 b (N : ℝ≥0) ω := by
      rw [hcc, one_mul]
    rw [hval, hreal, ← Real.exp_add]
    congr 1
    linarith
  have hDCT := tendsto_integral_of_dominated_convergence (fun _ => Real.exp (2 * c * b))
    (fun N => (hkey N).1.aestronglyMeasurable) (integrable_const _) hbound hlim
  have hone : ∫ ω, Real.exp (2 * c * b) * Real.exp (-(hitDrift (fun t ω => -B t ω) 0 b ω).toReal) ∂P = 1 :=
    tendsto_nhds_unique hDCT (tendsto_const_nhds.congr fun N => ((hkey N).2).symm)
  rw [integral_const_mul] at hone
  rw [eq_inv_of_mul_eq_one_right hone, ← Real.exp_neg, h2c]

/-- **The Laplace transform of the Brownian first passage time, strict form.** For a real Brownian motion with
continuous paths and `b > 0`, the first passage time `τ_b` strictly below `B 0 - b` of the path extended to `ℝ`
satisfies `E e^{-τ_b} = e^{-√2 b}`. -/
theorem integral_exp_neg_firstPassageBelow [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ} (hb : 0 < b) :
    ∫ ω, Real.exp (-firstPassageBelow (nnExtend fun t => B t ω) 0 b) ∂P = Real.exp (-(√2 * b)) := by
  rw [← integral_exp_neg_hitDrift_neg hB hm hcont hb]
  refine integral_congr_ae ?_
  have hall := ae_all_iff.2 fun N : ℕ => ae_firstPassageBelow_eq_hitDriftTrunc hB hm hcont b (N : ℝ≥0)
  filter_upwards [hall, ae_hitDrift_neg_lt_top hB hm hcont b] with ω hω hfin
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hfin.ne
  have hTN : hitDrift (fun t ω => -B t ω) 0 b ω ≤ ((n : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_natCast]
    exact hn.le
  have hco := coe_hitDriftTrunc_of_le (fun t ω => -B t ω) 0 b (n : ℝ≥0) ω hTN
  show Real.exp (-firstPassageBelow (nnExtend fun t => B t ω) 0 b) =
    Real.exp (-(hitDrift (fun t ω => -B t ω) 0 b ω).toReal)
  rw [(hω n hTN).1, ← hco, ENNReal.coe_toReal]

end LatticeProb.LadderSet
