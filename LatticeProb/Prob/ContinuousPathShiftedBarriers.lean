/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import LatticeProb.Prob.ContinuousPathOpenBarrier

/-!
# Measurability of shifted path barriers

Countable families of weak barriers for shifted continuous paths are measurable.
-/

open Set MeasureTheory

namespace LatticeProb

/-- Simultaneous weak lower barriers for countably many shifted paths are
measurable. Durations and shift speeds may have either sign. -/
theorem measurableSet_continuousPath_shiftedBarriers {Ω ι : Type*}
    [MeasurableSpace Ω] [Countable ι] (X : ι → Ω → ℝ → ℝ)
    (C : ι → Ω → ℝ) (a v d : ι → ℝ)
    (hcont : ∀ i ω, Continuous (X i ω))
    (hX : ∀ i t, Measurable (fun ω => X i ω t))
    (hC : ∀ i, Measurable (C i)) :
    MeasurableSet {ω | ∀ i, ∀ s ∈ Ioo 0 (d i),
      X i ω (a i) - C i ω ≤ X i ω (a i + v i * s)} := by
  apply measurableSet_setOfPred.2
  apply Measurable.forall
  intro i
  apply measurableSet_setOfPred.1
  exact measurableSet_continuousPath_openBarrier
    (fun ω s => X i ω (a i + v i * s))
    (fun ω => X i ω (a i) - C i ω) 0 (d i)
    (fun ω => (hcont i ω).comp (continuous_const.add (continuous_const.mul continuous_id)))
    (fun s => hX i (a i + v i * s)) ((hX i (a i)).sub (hC i))

end LatticeProb
