import LatticeProb.LQG.ConeLastLevelAttainment
import LatticeProb.LQG.LastLevelIncrement
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OConeZero

/-! # Increments of cone radial last-level times -/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MatedCRTHarmonic.ConeScaling

/-- A cone radial last-level increment has the law of the negated last-level
    time at the difference of the levels. -/
theorem map_cone_lastLevel_increment {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {γ α : ℝ}
    (hαQ : α < CellScaling.lqgQ γ) {B B' : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (QuantumZipper.pathOf B) (QuantumZipper.pathOf B') P)
    {W : Ω → C(ℝ, ℝ)} (hWm : Measurable W)
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ α
      (fun s => B s ω) (fun s => B' s ω) t)
    {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    P.map (fun ω => lastLevel (CellScaling.lqgQ γ) b (W ω) -
        lastLevel (CellScaling.lqgQ γ) a (W ω)) =
      P.map (fun ω => -lastLevel (CellScaling.lqgQ γ) (a - b) (W ω)) := by
  have hatt := ae_isGreatest_lastLevel_nonneg hαQ hB hB' hW
  have hgreat : ∀ᵐ ω ∂P, IsGreatest
      {s : ℝ | W ω (-s) + CellScaling.lqgQ γ * s = a}
      (lastLevel (CellScaling.lqgQ γ) a (W ω)) := by
    filter_upwards [hatt] with ω hω
    exact hω a ha
  have hshift := IGLaw.map_radShift_coneRadial_alpha hαQ hB hB' hBB' hWm hW b
  have hmap := map_lastLevel_sub_eq_of_radShift_invariant hWm
    (CellScaling.lqgQ γ) a b hgreat hshift
  have hmeas : Measurable (fun ω => lastLevel (CellScaling.lqgQ γ) a (W ω) -
      lastLevel (CellScaling.lqgQ γ) b (W ω)) :=
    ((measurable_lastLevel _ _).comp hWm).sub ((measurable_lastLevel _ _).comp hWm)
  have hmeas' : Measurable (fun ω => lastLevel (CellScaling.lqgQ γ) (a - b) (W ω)) :=
    (measurable_lastLevel _ _).comp hWm
  have hneg := congrArg (fun μ : Measure ℝ => μ.map (fun x : ℝ => -x)) hmap
  rw [Measure.map_map measurable_neg hmeas, Measure.map_map measurable_neg hmeas'] at hneg
  simpa only [Function.comp_def, neg_sub] using hneg

end MatedCRTHarmonic.ConeScaling
