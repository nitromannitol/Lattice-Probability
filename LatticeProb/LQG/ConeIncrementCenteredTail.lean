import LatticeProb.LQG.ConeIncrementHitLaw
import LatticeProb.Prob.BrownianDriftHitScaleTransfer
import LatticeProb.Prob.BrownianDriftExitMoment

/-! # Centered bounds for cone radial last-level increments -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.ConeScaling

/-- A cone radial last-level increment inherits the centered Gaussian tails
of its drifted Brownian hitting-time law. -/
theorem measure_cone_lastLevel_increment_outside_centered_le
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ α : ℝ} (hαQ : α < CellScaling.lqgQ γ) {B B' : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (hBB' : IndepFun (QuantumZipper.pathOf B) (QuantumZipper.pathOf B') P)
    {W : Ω → C(ℝ, ℝ)} (hWm : Measurable W)
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ α
      (fun s => B s ω) (fun s => B' s ω) t)
    {a b u : ℝ} (ha : 0 ≤ a) (hab : a < b) (hu : 0 < u)
    {Tlo Thi : ℝ≥0} (hlo : 0 < Tlo)
    (hloval : (Tlo : ℝ) = (b - a) / (CellScaling.lqgQ γ - α) - u)
    (hhi : 0 < Thi)
    (hhival : (Thi : ℝ) = (b - a) / (CellScaling.lqgQ γ - α) + u) :
    P {ω | ENNReal.ofReal (lastLevel (CellScaling.lqgQ γ) b (W ω) -
          lastLevel (CellScaling.lqgQ γ) a (W ω)) < (Tlo : ℝ≥0∞) ∨
        (Thi : ℝ≥0∞) < ENNReal.ofReal (lastLevel (CellScaling.lqgQ γ) b (W ω) -
          lastLevel (CellScaling.lqgQ γ) a (W ω))} ≤
      ENNReal.ofReal (Real.exp (-(((CellScaling.lqgQ γ - α) * u) ^ 2 / (2 * Tlo)))) +
      ENNReal.ofReal (Real.exp (-(((CellScaling.lqgQ γ - α) * u) ^ 2 / (2 * Thi)))) := by
  let X : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (lastLevel (CellScaling.lqgQ γ) b (W ω) - lastLevel (CellScaling.lqgQ γ) a (W ω))
  let N : ℝ≥0 → Ω → ℝ := fun t ω => -B t ω
  have hNm : ∀ t, Measurable (N t) := fun t => (hm t).neg
  have hNc : ∀ ω, Continuous fun t => N t ω := fun ω => (hcont ω).neg
  have hNX : Measurable X := ENNReal.measurable_ofReal.comp
    (((measurable_lastLevel _ _).comp hWm).sub ((measurable_lastLevel _ _).comp hWm))
  have hhit : Measurable (LatticeProb.hitDrift N (CellScaling.lqgQ γ - α) (b - a)) :=
    LatticeProb.measurable_of_isStoppingTime_enn
      (LatticeProb.isStoppingTime_hitDrift_brownian hNm hNc _ _)
  have hmap := map_ofReal_cone_lastLevel_increment_eq_hitDrift hαQ hB hB' hBB' hWm hW ha hab
  have hlaw : ∀ s : Set ℝ≥0∞, MeasurableSet s → P {ω | X ω ∈ s} =
      P {ω | LatticeProb.hitDrift N (CellScaling.lqgQ γ - α) (b - a) ω ∈ s} := by
    intro s hs
    change P (X ⁻¹' s) = P ((LatticeProb.hitDrift N (CellScaling.lqgQ γ - α) (b - a)) ⁻¹' s)
    rw [← Measure.map_apply hNX hs, ← Measure.map_apply hhit hs]
    exact congrArg (fun μ : Measure ℝ≥0∞ => μ s) hmap
  exact LatticeProb.measure_hitLaw_outside_centered_le hB.neg hNm hNc
    (sub_pos.mpr hαQ) hu hlo hloval hhi hhival X hlaw

end MatedCRTHarmonic.ConeScaling
