import LatticeProb.Topology.FirstExitBallSelection

/-! # Directional first-exit ball bounds -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- Failure of finite forward-exit ball containment at a fixed scale. -/
noncomputable def forwardExitBallFailure {β : Type*} {d : ℕ}
    (f : β → C(ℝ, EuclideanSpace ℝ (Fin d))) (ε : ℝ) (k : ℤ) : Set β :=
  {ω | ¬ (openExitTime (fun s (_ : Unit) => f ω (0 + (s : ℝ)))
      (ball 0 (Real.exp (k : ℝ))) () ≠ ⊤ ∧
    0 ≤ ε * Real.exp (k : ℝ) / 2 ∧ ∃ z,
      closedBall z (ε * Real.exp (k : ℝ) / 2) ⊆
        f ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ f ω t ∉ ball 0 (Real.exp (k : ℝ))}))}

/-- Failure of finite backward-exit ball containment at a fixed scale. -/
noncomputable def backwardExitBallFailure {β : Type*} {d : ℕ}
    (f : β → C(ℝ, EuclideanSpace ℝ (Fin d))) (ε : ℝ) (k : ℤ) : Set β :=
  {ω | ¬ (openExitTime (fun s (_ : Unit) => f ω (0 - (s : ℝ)))
      (ball 0 (Real.exp (k : ℝ))) () ≠ ⊤ ∧
    0 ≤ ε * Real.exp (k : ℝ) / 2 ∧ ∃ z,
      closedBall z (ε * Real.exp (k : ℝ) / 2) ⊆
        f ω '' Icc (sSup {t : ℝ | t ≤ 0 ∧ f ω t ∉ ball 0 (Real.exp (k : ℝ))}) 0)}

/-- Separate directional estimates bound the combined failure probability. -/
theorem measure_firstExitBallFailure_le_of_directional
    {β : Type*} [MeasurableSpace β] {d : ℕ} (ν : Measure β)
    (f : β → C(ℝ, EuclideanSpace ℝ (Fin d))) (ε : ℝ) (k : ℤ)
    (p q : ℝ≥0∞) (hp : ν (forwardExitBallFailure f ε k) ≤ p)
    (hq : ν (backwardExitBallFailure f ε k) ≤ q) :
    ν (firstExitBallFailure f ε k) ≤ p + q := by
  have heq : firstExitBallFailure f ε k =
      forwardExitBallFailure f ε k ∪ backwardExitBallFailure f ε k := by
    ext ω
    simp only [firstExitBallFailure, forwardExitBallFailure, backwardExitBallFailure,
      mem_ofPred_eq, mem_union, not_and_or]
  rw [heq]
  exact (measure_union_le _ _).trans (add_le_add hp hq)

/-- Separate directional estimates also control failures at a random finite selection. -/
theorem prod_measure_exists_mem_firstExitBallFailure_le_of_directional
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {d : ℕ}
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : α → Finset ℤ) (hK : Measurable K)
    {f : β → C(ℝ, EuclideanSpace ℝ (Fin d))} (hf : Measurable f)
    (ε : ℝ) (p q : ℝ≥0∞) (N : ℕ)
    (hp : ∀ k, ν (forwardExitBallFailure f ε k) ≤ p)
    (hq : ∀ k, ν (backwardExitBallFailure f ε k) ≤ q) :
    (μ.prod ν) {z : α × β | ∃ k ∈ K z.1, z.2 ∈ firstExitBallFailure f ε k} ≤
      μ {x | N < (K x).card} + (N : ℝ≥0∞) * (p + q) := by
  apply prod_measure_exists_mem_firstExitBallFailure_le μ ν K hK hf ε (p + q) N
  intro k
  exact measure_firstExitBallFailure_le_of_directional ν f ε k p q (hp k) (hq k)

end LatticeProb
