import LatticeProb.Prob.BrownianPathSpace
import LatticeProb.Prob.BrownianDirichlet.ScaledExit
import LatticeProb.Prob.BrownianDirichlet.JointMeasurability

/-!
# Exit from large balls

A continuous path on a finite time interval stays inside a sufficiently large ball.
Continuity from above then makes the probability of exit by that time tend to zero.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace LatticeProb

variable {d : ℕ}

/-- The norm of a continuous function is bounded by an integer on a compact time interval. -/
lemma exists_nat_norm_lt_on_Icc {E : Type*} [NormedAddCommGroup E]
    {f : ℝ≥0 → E} (hf : Continuous f) (T : ℝ≥0) :
    ∃ R : ℕ, ∀ t ∈ Icc (0 : ℝ≥0) T, ‖f t‖ < (R : ℝ) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.image hf).isBounded.exists_norm_le
  obtain ⟨R, hR⟩ := exists_nat_gt M
  exact ⟨R, fun t ht ↦ (hM _ ⟨t, ht, rfl⟩).trans_lt hR⟩

/-- A shifted scaled continuous path stays in some integer-radius ball up to a finite time. -/
theorem exists_largeBall_no_exit (s : ℝ) (x : Euc d) (ω : BrownianPath d)
    (T : ℝ≥0) :
    ∃ R : ℕ, ¬ continuousExitTime (Metric.ball 0 (R : ℝ)) x (scalePath s ω) ≤
      (T : ℝ≥0∞) := by
  have hc : Continuous (fun t : ℝ≥0 ↦ x + s • ω t) :=
    continuous_const.add (ω.continuous.const_smul s)
  obtain ⟨R, hR⟩ := exists_nat_norm_lt_on_Icc hc T
  refine ⟨R, ?_⟩
  change ¬ scaledExit (Metric.ball 0 (R : ℝ)) s x ω ≤ (T : ℝ≥0∞)
  rw [scaledExit_le_iff Metric.isOpen_ball]
  apply not_not.mpr
  intro t ht
  rw [Metric.mem_ball, dist_zero_right]
  exact hR t ⟨zero_le, ht⟩

/-- Under any finite joint law, exit from growing balls before a finite time has vanishing mass. -/
theorem tendsto_exit_largeBall_measure (ν : Measure (Euc d × BrownianPath d))
    [IsFiniteMeasure ν] (s : ℝ) (T : ℝ≥0) :
    Tendsto (fun R : ℕ ↦ ν {p | continuousExitTime (Metric.ball 0 (R : ℝ)) p.1
      (scalePath s p.2) ≤ (T : ℝ≥0∞)}) atTop (𝓝 0) := by
  let A : ℕ → Set (Euc d × BrownianPath d) := fun R ↦
    {p | scaledExit (Metric.ball 0 (R : ℝ)) s p.1 p.2 ≤ (T : ℝ≥0∞)}
  have hm (R : ℕ) : MeasurableSet (A R) :=
    measurableSet_le (measurable_scaledExit_joint Metric.isOpen_ball s) measurable_const
  have hanti : Antitone A := by
    intro R S hRS p hp
    change scaledExit (Metric.ball 0 (S : ℝ)) s p.1 p.2 ≤ (T : ℝ≥0∞) at hp
    change scaledExit (Metric.ball 0 (R : ℝ)) s p.1 p.2 ≤ (T : ℝ≥0∞)
    rw [scaledExit_le_iff Metric.isOpen_ball] at hp ⊢
    intro h
    apply hp
    intro t ht
    exact Metric.ball_subset_ball (by exact_mod_cast hRS) (h t ht)
  have hempty : (⋂ R, A R) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨R, hR⟩ := exists_largeBall_no_exit s p.1 p.2 T
    exact hR (mem_iInter.mp hp R)
  have hlim := tendsto_measure_iInter_atTop (fun R ↦ (hm R).nullMeasurableSet)
    hanti ⟨0, measure_ne_top ν _⟩
  rw [hempty, measure_empty] at hlim
  exact hlim

/-- Independent initial and continuous-path laws have vanishing large-ball exit probability. -/
theorem tendsto_exit_largeBall (ρ : Measure (Euc d)) [IsProbabilityMeasure ρ]
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (s : ℝ) (T : ℝ≥0) :
    Tendsto (fun R : ℕ ↦ (ρ.prod μ) {p | continuousExitTime
      (Metric.ball 0 (R : ℝ)) p.1 (scalePath s p.2) ≤ (T : ℝ≥0∞)})
      atTop (𝓝 0) :=
  tendsto_exit_largeBall_measure (ρ.prod μ) s T

/-- Standard Brownian laws satisfy the large-ball exit limit for every spatial scale. -/
theorem tendsto_exit_largeBall_brownian (ρ : Measure (Euc d)) [IsProbabilityMeasure ρ]
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (s : ℝ) (T : ℝ≥0) :
    Tendsto (fun R : ℕ ↦ (ρ.prod μ) {p | continuousExitTime
      (Metric.ball 0 (R : ℝ)) p.1 (scalePath s p.2) ≤ (T : ℝ≥0∞)})
      atTop (𝓝 0) := by
  letI : IsProbabilityMeasure μ := hμ.1
  exact tendsto_exit_largeBall ρ μ s T

end LatticeProb
