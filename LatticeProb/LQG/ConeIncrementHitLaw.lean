import LatticeProb.LQG.ConeLastLevelIncrement
import LatticeProb.LQG.ConeNegativeLevelHit

/-! # Hitting-time law for cone radial last-level increments -/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MatedCRTHarmonic.ConeScaling

/-- A positive increment of cone radial levels has the law of the first passage
    time of Brownian motion with positive drift. -/
theorem map_ofReal_cone_lastLevel_increment_eq_hitDrift
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ α : ℝ} (hαQ : α < CellScaling.lqgQ γ) {B B' : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (QuantumZipper.pathOf B) (QuantumZipper.pathOf B') P)
    {W : Ω → C(ℝ, ℝ)} (hWm : Measurable W)
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ α
      (fun s => B s ω) (fun s => B' s ω) t)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    P.map (fun ω => ENNReal.ofReal (lastLevel (CellScaling.lqgQ γ) b (W ω) -
        lastLevel (CellScaling.lqgQ γ) a (W ω))) =
      P.map (LatticeProb.hitDrift (fun t ω => -B t ω)
        (CellScaling.lqgQ γ - α) (b - a)) := by
  have hinc : Measurable (fun ω => lastLevel (CellScaling.lqgQ γ) b (W ω) -
      lastLevel (CellScaling.lqgQ γ) a (W ω)) :=
    ((measurable_lastLevel _ _).comp hWm).sub ((measurable_lastLevel _ _).comp hWm)
  have hneg : Measurable (fun ω => -lastLevel (CellScaling.lqgQ γ) (a - b) (W ω)) :=
    ((measurable_lastLevel _ _).comp hWm).neg
  have hlaw := map_cone_lastLevel_increment hαQ hB hB' hBB' hWm hW ha b
  have hmap := congrArg (fun μ : Measure ℝ => μ.map ENNReal.ofReal) hlaw
  rw [Measure.map_map ENNReal.measurable_ofReal hinc,
    Measure.map_map ENNReal.measurable_ofReal hneg] at hmap
  have hhit := ae_ofReal_neg_lastLevel_eq_hitDrift hαQ hB hB' hBB' hW
    (sub_neg.mpr hab)
  have heq : (fun ω => ENNReal.ofReal (-lastLevel (CellScaling.lqgQ γ) (a - b) (W ω))) =ᵐ[P]
      LatticeProb.hitDrift (fun t ω => -B t ω) (CellScaling.lqgQ γ - α) (b - a) := by
    filter_upwards [hhit] with ω hω
    simpa only [neg_sub] using hω
  calc
    _ = P.map (fun ω => ENNReal.ofReal (-lastLevel (CellScaling.lqgQ γ) (a - b) (W ω))) := by
      simpa only [Function.comp_def] using hmap
    _ = _ := Measure.map_congr heq

end MatedCRTHarmonic.ConeScaling
