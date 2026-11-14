/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianInnerExit at commit fdb5cad; local import paths and linter settings are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.ContinuousExitProperties
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option linter.style.haveILetI false

/-! The inner boundary approach uses the actual first exit from the open set
of points whose distance to the complement exceeds the prescribed clearance. -/

open Set Metric
open scoped NNReal ENNReal

namespace BouRabeeGwynne

def innerDomain {d : ℕ} (U : Set (Euc d)) (ε : ℝ) : Set (Euc d) :=
  {x | ε < infDist x Uᶜ}

lemma isOpen_innerDomain {d : ℕ} (U : Set (Euc d)) (ε : ℝ) :
    IsOpen (innerDomain U ε) :=
  isOpen_lt continuous_const (continuous_infDist_pt Uᶜ)

lemma closure_innerDomain_subset {d : ℕ} (U : Set (Euc d)) {ε : ℝ} (hε : 0 < ε) :
    closure (innerDomain U ε) ⊆ U := by
  intro x hx
  have hdist : ε ≤ infDist x Uᶜ :=
    closure_lt_subset_le continuous_const (continuous_infDist_pt Uᶜ) hx
  by_contra hout
  rw [infDist_zero_of_mem hout] at hdist
  exact (not_le_of_gt hε) hdist

lemma frontier_innerDomain_infDist {d : ℕ} (U : Set (Euc d)) (ε : ℝ)
    {x : Euc d} (hx : x ∈ frontier (innerDomain U ε)) :
    infDist x Uᶜ = ε :=
  (frontier_lt_subset_eq continuous_const (continuous_infDist_pt Uᶜ) hx).symm

lemma closedBall_subset_of_mem_innerDomain {d : ℕ} {U : Set (Euc d)} {ε : ℝ}
    {x : Euc d} (hx : x ∈ innerDomain U ε) : closedBall x ε ⊆ U := by
  intro y hy
  by_contra hout
  have hdist : infDist x Uᶜ ≤ ε := (infDist_le_dist_of_mem hout).trans
    (by simpa only [mem_closedBall, dist_comm] using hy)
  exact (not_le_of_gt hx) hdist

lemma innerExit_position {d : ℕ} {U : Set (Euc d)} {ε : ℝ} (hε : 0 < ε)
    {z : Euc d} (hz : z ∈ U) {ω : BrownianPath d} (hzero : ω 0 = 0)
    (hfinite : continuousExitTime (innerDomain U ε) z ω ≠ ∞) :
    let x := z + ω (continuousExitTime (innerDomain U ε) z ω).toNNReal
    x ∈ U ∧ infDist x Uᶜ ≤ ε := by
  by_cases hin : z ∈ innerDomain U ε
  · have hfront := continuousExitTime_mem_frontier (isOpen_innerDomain U ε)
      (by simpa only [hzero, add_zero] using hin) hfinite
    exact ⟨closure_innerDomain_subset U hε (frontier_subset_closure hfront),
      (frontier_innerDomain_infDist U ε hfront).le⟩
  · have htime : continuousExitTime (innerDomain U ε) z ω = 0 :=
      continuousExitTime_eq_zero_of_not_mem (by simpa only [hzero, add_zero] using hin)
    simp only [htime, ENNReal.toNNReal_zero, hzero, add_zero]
    exact ⟨hz, le_of_not_gt hin⟩

/-- The actual inner exit is within the prescribed clearance of the original
boundary, including when the inner exit occurs immediately at time zero. -/
lemma innerExit_exists_frontier_near {d : ℕ} (hd : 1 ≤ d)
    {U : Set (Euc d)} (hU : Bornology.IsBounded U) {ε : ℝ} (hε : 0 < ε)
    {z : Euc d} (hz : z ∈ U) {ω : BrownianPath d} (hzero : ω 0 = 0)
    (hfinite : continuousExitTime (innerDomain U ε) z ω ≠ ∞) :
    ∃ p ∈ frontier U,
      dist (z + ω (continuousExitTime (innerDomain U ε) z ω).toNNReal) p ≤ ε := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hne : U ≠ univ := by
    intro h
    exact hU.isCompact_closure.ne_univ (by simp only [h, closure_univ])
  obtain ⟨hx, hclear⟩ := innerExit_position hε hz hzero hfinite
  obtain ⟨p, hp, heq⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hne
  exact ⟨p, hp, heq.symm.le.trans hclear⟩

end BouRabeeGwynne
