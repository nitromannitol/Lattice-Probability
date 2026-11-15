import LatticeProb.Topology.FirstExitBallDirectional

/-! # Open-ball estimates for first-exit traces -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- Failure of finite forward-exit open-ball containment at a fixed scale. -/
noncomputable def forwardExitOpenBallFailure {β : Type*} {d : ℕ}
    (f : β → C(ℝ, EuclideanSpace ℝ (Fin d))) (ε : ℝ) (k : ℤ) : Set β :=
  {ω | ¬ (openExitTime (fun s (_ : Unit) => f ω (0 + (s : ℝ)))
      (ball 0 (Real.exp (k : ℝ))) () ≠ ⊤ ∧ ∃ z,
      ball z (ε * Real.exp (k : ℝ)) ⊆
        f ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ f ω t ∉ ball 0 (Real.exp (k : ℝ))}))}

/-- Failure of finite backward-exit open-ball containment at a fixed scale. -/
noncomputable def backwardExitOpenBallFailure {β : Type*} {d : ℕ}
    (f : β → C(ℝ, EuclideanSpace ℝ (Fin d))) (ε : ℝ) (k : ℤ) : Set β :=
  {ω | ¬ (openExitTime (fun s (_ : Unit) => f ω (0 - (s : ℝ)))
      (ball 0 (Real.exp (k : ℝ))) () ≠ ⊤ ∧ ∃ z,
      ball z (ε * Real.exp (k : ℝ)) ⊆
        f ω '' Icc (sSup {t : ℝ | t ≤ 0 ∧ f ω t ∉ ball 0 (Real.exp (k : ℝ))}) 0)}

/-- A positive-radius open-ball estimate controls forward closed-ball failure. -/
theorem forwardExitBallFailure_subset_open {β : Type*} {d : ℕ}
    (f : β → C(ℝ, EuclideanSpace ℝ (Fin d))) {ε : ℝ} (hε : 0 < ε) (k : ℤ) :
    forwardExitBallFailure f ε k ⊆ forwardExitOpenBallFailure f ε k := by
  intro ω hfail hgood
  apply hfail
  obtain ⟨hfinite, z, hz⟩ := hgood
  have hpos : 0 < ε * Real.exp (k : ℝ) := mul_pos hε (Real.exp_pos _)
  exact ⟨hfinite, (half_pos hpos).le, z,
    (closedBall_subset_ball (half_lt_self hpos)).trans hz⟩

/-- A positive-radius open-ball estimate controls backward closed-ball failure. -/
theorem backwardExitBallFailure_subset_open {β : Type*} {d : ℕ}
    (f : β → C(ℝ, EuclideanSpace ℝ (Fin d))) {ε : ℝ} (hε : 0 < ε) (k : ℤ) :
    backwardExitBallFailure f ε k ⊆ backwardExitOpenBallFailure f ε k := by
  intro ω hfail hgood
  apply hfail
  obtain ⟨hfinite, z, hz⟩ := hgood
  have hpos : 0 < ε * Real.exp (k : ℝ) := mul_pos hε (Real.exp_pos _)
  exact ⟨hfinite, (half_pos hpos).le, z,
    (closedBall_subset_ball (half_lt_self hpos)).trans hz⟩

/-- Open-ball directional estimates control failures at a random finite selection. -/
theorem prod_measure_exists_mem_firstExitBallFailure_le_of_open_directional
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {d : ℕ}
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : α → Finset ℤ) (hK : Measurable K)
    {f : β → C(ℝ, EuclideanSpace ℝ (Fin d))} (hf : Measurable f)
    {ε : ℝ} (hε : 0 < ε) (p q : ℝ≥0∞) (N : ℕ)
    (hp : ∀ k, ν (forwardExitOpenBallFailure f ε k) ≤ p)
    (hq : ∀ k, ν (backwardExitOpenBallFailure f ε k) ≤ q) :
    (μ.prod ν) {z : α × β | ∃ k ∈ K z.1, z.2 ∈ firstExitBallFailure f ε k} ≤
      μ {x | N < (K x).card} + (N : ℝ≥0∞) * (p + q) := by
  apply prod_measure_exists_mem_firstExitBallFailure_le_of_directional μ ν K hK hf ε p q N
  · intro k
    exact (measure_mono (forwardExitBallFailure_subset_open f hε k)).trans (hp k)
  · intro k
    exact (measure_mono (backwardExitBallFailure_subset_open f hε k)).trans (hq k)

end LatticeProb
