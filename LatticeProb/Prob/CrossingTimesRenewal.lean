import Mathlib
import LatticeProb.Prob.CrossingTimesRestart
import LatticeProb.Prob.BrownianOpenExitFinite
import LatticeProb.Analysis.CrossingTimesShift

/-!
# The crossing times of a Brownian motion are almost surely finite

For a Brownian motion `B` in `ℝ ^ d`, `d ≥ 1`, and `ε > 0`, every `ε`-crossing time
`crossTime ε (B · ω) k` is finite almost surely.  The first crossing time is the first exit time
from the open ball of radius `ε` around the starting point, which is finite almost surely.  The
`(k+1)`-st crossing time is the `k`-th one plus the first crossing time of the motion restarted
at the `k`-th one; the restarted motion has the law of the centred motion, so the induction
closes with the strong Markov property at an almost surely finite stopping time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

omit [MeasurableSpace Ω] in
/-- The first `ε`-crossing time of a path started at `x` is at most the first exit time from the
open ball of radius `ε` around `x`. -/
theorem crossTime_one_le_openExitTime {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    {x : EuclideanSpace ℝ (Fin d)} {ω : Ω} (hx : B 0 ω = x) {ε : ℝ} (hε : 0 < ε) :
    crossTime ε (fun t => B t ω) 1 ≤ openExitTime B (Metric.ball x ε) ω := by
  rw [crossTime_one_eq]
  refine le_iInf fun t => ?_
  have ht : ε ≤ dist (B t.1 ω) x := by
    have h := t.2
    simpa [Metric.mem_ball, not_lt] using h
  have ht0 : (0 : ℝ≥0) < t.1 := by
    rcases eq_or_ne t.1 0 with h | h
    · exfalso
      have h0 := t.2
      rw [h, hx] at h0
      exact h0 (Metric.mem_ball_self hε)
    · exact pos_iff_ne_zero.2 h
  exact nextCrossTime_le_of_lt (by exact_mod_cast ht0) (by simpa [hx] using ht)

/-- The first `ε`-crossing time of a Brownian motion is finite almost surely. -/
theorem ae_crossTime_one_ne_top (hd : 1 ≤ d) {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P) {ε : ℝ}
    (hε : 0 < ε) : ∀ᵐ ω ∂P, crossTime ε (fun t => B t ω) 1 ≠ ⊤ := by
  filter_upwards [hB.start, ae_openExitTime_ne_top hd hB (Metric.isBounded_ball (x := x) (r := ε))]
    with ω hω hne
  exact ne_top_of_le_ne_top hne (crossTime_one_le_openExitTime hω hε)

/-- The first `ε`-crossing time of the centred motion is finite almost surely. -/
theorem ae_crossTime_restartPath_zero_ne_top (hd : 1 ≤ d) {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P)
    (hcont : ∀ ω, Continuous fun t => B t ω) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, crossTime ε (fun s => restartPath B hcont (fun _ => 0) ω s) 1 ≠ ⊤ := by
  filter_upwards [ae_crossTime_one_ne_top hd hB hε] with ω hω
  have h : (fun s => restartPath B hcont (fun _ => 0) ω s) =
      fun s => (fun t => B t ω) s - B 0 ω := by
    funext s
    simp [restartPath]
  have h2 := congrFun (crossTime_sub_const ε (fun t => B t ω) (B 0 ω)) 1
  have h3 : crossTime ε (fun s => restartPath B hcont (fun _ => 0) ω s) 1 =
      crossTime ε (fun t => B t ω) 1 := by
    rw [h]
    exact h2
  rw [h3]
  exact hω

/-- **Every crossing time of a Brownian motion is finite almost surely.** -/
theorem ae_crossTime_ne_top (hd : 1 ≤ d) {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P)
    [IsProbabilityMeasure P] (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    ∀ᵐ ω ∂P, crossTime ε (fun t => B t ω) k ≠ ⊤ := by
  induction k with
  | zero => exact Eventually.of_forall fun ω => by simp [crossTime_zero]
  | succ k ih =>
    have hσ := isStoppingTime_crossTime_natFiltration B hm hcont hε k
    have hS : MeasurableSet {γ : BrownianPath d | crossTime ε (fun s => γ s) 1 = ⊤} :=
      (measurable_crossTime (E := Euc d) hε 1) (measurableSet_singleton ⊤)
    have hP := hB.restart_ennreal hm hcont hσ ih (E := Set.univ) MeasurableSet.univ hS
    have h0 : P {ω | restartPath B hcont (fun _ => 0) ω ∈
        {γ : BrownianPath d | crossTime ε (fun s => γ s) 1 = ⊤}} = 0 := by
      refine measure_eq_zero_iff_ae_notMem.2 ?_
      filter_upwards [ae_crossTime_restartPath_zero_ne_top hd hB hcont hε] with ω hω
      exact hω
    rw [h0, mul_zero, Set.univ_inter] at hP
    filter_upwards [ih, measure_eq_zero_iff_ae_notMem.1 hP] with ω hω1 hω2
    rw [crossTime_succ_eq_add]
    refine ENNReal.add_ne_top.2 ⟨hω1, ?_⟩
    set s : ℝ≥0 := (crossTime ε (fun t => B t ω) k).toNNReal with hs
    have h4 := congrFun (crossTime_sub_const ε (fun u => B (s + u) ω) (B s ω)) 1
    rw [← h4]
    exact hω2

end LatticeProb
