import LatticeProb.Prob.BallExitSegmentBallAE

/-! # Filtration of nested ball-exit histories -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open scoped NNReal ENNReal

namespace LatticeProb

/-- The natural filtration stopped at the exits from an increasing sequence of balls. -/
noncomputable def ballExitHistory {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    (z : EuclideanSpace ℝ (Fin d)) (r : ℕ → ℝ) (hr : Monotone r) :
    Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq k := (isStoppingTime_openExitTime hm hc
    (isOpen_ball : IsOpen (ball z (r k)))).measurableSpace
  mono' i j hij := (isStoppingTime_openExitTime hm hc
    (isOpen_ball : IsOpen (ball z (r i)))).measurableSpace_mono
      (isStoppingTime_openExitTime hm hc (isOpen_ball : IsOpen (ball z (r j))))
      (fun ω => monotone_openExitTime_ball X ω z (hr hij))
  le' k := (isStoppingTime_openExitTime hm hc
    (isOpen_ball : IsOpen (ball z (r k)))).measurableSpace_le

/-- A nested exit segment's ball-containment event has an adapted representative when the
outer exit is almost surely finite. -/
theorem exists_measurableSet_ball_subset_exitHistory_segment
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
    {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    (z : EuclideanSpace ℝ (Fin d)) (r : ℕ → ℝ) (hr : Monotone r)
    (k : ℕ) {a : ℝ} (ha : 0 < a)
    (hfin : ∀ᵐ ω ∂μ, openExitTime X (ball z (r (k + 1))) ω ≠ ⊤) :
    ∃ s : Set Ω, MeasurableSet[ballExitHistory X hm hc z r hr (k + 1)] s ∧
      ∀ᵐ ω ∂μ, (ω ∈ s ↔ ∃ w, ball w a ⊆ (fun t : ℝ => X t.toNNReal ω) '' Icc
        ((openExitTime X (ball z (r k)) ω).toNNReal : ℝ)
        ((openExitTime X (ball z (r (k + 1))) ω).toNNReal : ℝ)) := by
  exact exists_measurableSet_ball_subset_nested_exit_segment_ae hm hc z
    (hr (Nat.le_succ k)) ha hfin

end LatticeProb
