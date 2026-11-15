import LatticeProb.Topology.MeasurableFirstExitTraceBall
import LatticeProb.Prob.RandomFiniteSelectionMeasurable

/-! # Fixed-scale first-exit ball events -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- Failure of forward or backward finite-exit ball containment at a fixed scale. -/
noncomputable def firstExitBallFailure {β : Type*} {d : ℕ}
    (f : β → C(ℝ, EuclideanSpace ℝ (Fin d))) (ε : ℝ) (k : ℤ) : Set β :=
  {ω | ¬ ((openExitTime (fun s (_ : Unit) => f ω (0 + (s : ℝ)))
      (ball 0 (Real.exp (k : ℝ))) () ≠ ⊤ ∧
    0 ≤ ε * Real.exp (k : ℝ) / 2 ∧ ∃ z,
      closedBall z (ε * Real.exp (k : ℝ) / 2) ⊆
        f ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ f ω t ∉ ball 0 (Real.exp (k : ℝ))})) ∧
    (openExitTime (fun s (_ : Unit) => f ω (0 - (s : ℝ)))
      (ball 0 (Real.exp (k : ℝ))) () ≠ ⊤ ∧
    0 ≤ ε * Real.exp (k : ℝ) / 2 ∧ ∃ z,
      closedBall z (ε * Real.exp (k : ℝ) / 2) ⊆
        f ω '' Icc (sSup {t : ℝ | t ≤ 0 ∧ f ω t ∉ ball 0 (Real.exp (k : ℝ))}) 0))}

/-- The fixed-scale failure event is measurable for a measurable random curve. -/
theorem measurableSet_firstExitBallFailure {β : Type*} [MeasurableSpace β] {d : ℕ}
    {f : β → C(ℝ, EuclideanSpace ℝ (Fin d))} (hf : Measurable f)
    (ε : ℝ) (k : ℤ) : MeasurableSet (firstExitBallFailure f ε k) := by
  have hfwd := measurableSet_forward_firstExitTrace_contains_closedBall hf
    (measurable_const : Measurable (fun _ : β => ε * Real.exp (k : ℝ) / 2))
    (ball 0 (Real.exp (k : ℝ))) isOpen_ball 0
  have hbwd := measurableSet_backward_firstExitTrace_contains_closedBall hf
    (measurable_const : Measurable (fun _ : β => ε * Real.exp (k : ℝ) / 2))
    (ball 0 (Real.exp (k : ℝ))) isOpen_ball 0
  exact (hfwd.inter hbwd).compl

/-- A random finite selection of fixed-scale failures satisfies a product-law union bound. -/
theorem prod_measure_exists_mem_firstExitBallFailure_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {d : ℕ}
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : α → Finset ℤ) (hK : Measurable K)
    {f : β → C(ℝ, EuclideanSpace ℝ (Fin d))} (hf : Measurable f)
    (ε : ℝ) (p : ℝ≥0∞) (N : ℕ)
    (hfail : ∀ k, ν (firstExitBallFailure f ε k) ≤ p) :
    (μ.prod ν) {z : α × β | ∃ k ∈ K z.1, z.2 ∈ firstExitBallFailure f ε k} ≤
      μ {x | N < (K x).card} + (N : ℝ≥0∞) * p := by
  exact prod_measure_exists_mem_finset_le_of_measurable μ ν K
    (firstExitBallFailure f ε) p N hK (measurableSet_firstExitBallFailure hf ε) hfail

end LatticeProb
