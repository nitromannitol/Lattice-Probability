/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import LatticeProb.Prob.ContinuousPathShiftedBarriers
import LatticeProb.Prob.ContinuousPathClosedBarrier

/-!
# Measurability of path barrier events

Simultaneous local shifted barriers and closed-interval endpoint constraints
form a measurable event for a countable family of continuous paths.
-/

open Set MeasureTheory

namespace LatticeProb

/-- Countably many shifted weak barriers and closed-interval increment barriers
can be imposed simultaneously in a measurable event. -/
theorem measurableSet_continuousPath_barrierEvents {Ω ι κ : Type*}
    [MeasurableSpace Ω] [Countable ι] [Countable κ]
    (X : ι → Ω → ℝ → ℝ) (C : ι → Ω → ℝ) (a v d : ι → ℝ)
    (Y : κ → Ω → ℝ → ℝ) (D : κ → Ω → ℝ) (b c : κ → ℝ)
    (hXcont : ∀ i ω, Continuous (X i ω))
    (hX : ∀ i t, Measurable (fun ω => X i ω t))
    (hC : ∀ i, Measurable (C i))
    (hYcont : ∀ j ω, Continuous (Y j ω))
    (hY : ∀ j t, Measurable (fun ω => Y j ω t))
    (hD : ∀ j, Measurable (D j)) :
    MeasurableSet {ω |
      (∀ i, ∀ s ∈ Ioo 0 (d i),
        X i ω (a i) - C i ω ≤ X i ω (a i + v i * s)) ∧
      (∀ j, |Y j ω (c j) - Y j ω (b j)| ≤ D j ω ∧
        ∀ t ∈ Icc (b j) (c j), Y j ω (c j) - D j ω ≤ Y j ω t)} := by
  apply MeasurableSet.inter
  · exact measurableSet_continuousPath_shiftedBarriers X C a v d hXcont hX hC
  · apply measurableSet_setOfPred.2
    apply Measurable.forall
    intro j
    apply measurableSet_setOfPred.1
    exact measurableSet_continuousPath_increment_closedBarrier
      (Y j) (D j) (b j) (c j) (hYcont j) (hY j) (hD j)

end LatticeProb
