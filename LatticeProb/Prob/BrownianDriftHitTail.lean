import LatticeProb.Prob.BrownianTail
import LatticeProb.Prob.BrownianDriftRestartHit

/-! # Upper tail for the hitting time of Brownian motion with drift -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- If the drifted Brownian path has not reached a level by a positive time,
its terminal value gives a Gaussian upper bound for the hitting-time tail. -/
theorem measure_hitDrift_gt_le_exp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t => B t ω)
    {μ a : ℝ} {T : ℝ≥0} (hT : 0 < T) (ha : a < μ * T) :
    P {ω | (T : ℝ≥0∞) < hitDrift B μ a ω} ≤
      ENNReal.ofReal (Real.exp (-((μ * T - a) ^ 2 / (2 * T)))) := by
  have hpos : 0 < μ * (T : ℝ) - a := by linarith
  calc
    P {ω | (T : ℝ≥0∞) < hitDrift B μ a ω} ≤
        P {ω | μ * (T : ℝ) - a ≤ (-B) T ω} := by
      apply measure_mono
      intro ω hω
      have hnot : ¬ a ≤ B T ω + μ * T := by
        intro h
        exact (not_le_of_gt hω) ((hitDrift_le_iff hcont μ a ω T).2 ⟨T, le_rfl, h⟩)
      have hlt : B T ω + μ * (T : ℝ) < a := lt_of_not_ge hnot
      change μ * (T : ℝ) - a ≤ - B T ω
      linarith
    _ ≤ ENNReal.ofReal (Real.exp (-((μ * T - a) ^ 2 / (2 * T)))) :=
      measure_ge_le_exp hB.neg.toIsPreBrownianReal hT hpos

end LatticeProb
