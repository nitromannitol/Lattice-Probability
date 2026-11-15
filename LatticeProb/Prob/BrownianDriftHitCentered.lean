import LatticeProb.Prob.BrownianDriftHitTail
import LatticeProb.Prob.BrownianDriftHitLowerTail

/-! # Centered hitting-time bounds for Brownian motion with drift -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- The upper tail at a positive displacement from the deterministic drift time. -/
theorem measure_hitDrift_gt_centered_le_exp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t => B t ω)
    {μ a u : ℝ} {T : ℝ≥0} (hμ : 0 < μ) (hu : 0 < u)
    (hTpos : 0 < T) (hT : (T : ℝ) = a / μ + u) :
    P {ω | (T : ℝ≥0∞) < hitDrift B μ a ω} ≤
      ENNReal.ofReal (Real.exp (-((μ * u) ^ 2 / (2 * T)))) := by
  have hm : μ * (a / μ) = a := by field_simp [ne_of_gt hμ]
  have hgap : μ * (T : ℝ) - a = μ * u := by rw [hT]; nlinarith
  have ha : a < μ * (T : ℝ) := by nlinarith [mul_pos hμ hu]
  simpa only [hgap] using measure_hitDrift_gt_le_exp hB hcont hTpos ha

/-- The lower tail at a positive displacement from the deterministic drift time. -/
theorem measure_hitDrift_le_centered_le_exp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {μ a u : ℝ} {T : ℝ≥0} (hμ : 0 < μ) (hu : 0 < u)
    (hTpos : 0 < T) (hT : (T : ℝ) = a / μ - u) :
    P {ω | hitDrift B μ a ω ≤ (T : ℝ≥0∞)} ≤
      ENNReal.ofReal (Real.exp (-((μ * u) ^ 2 / (2 * T)))) := by
  have hma : μ * (a / μ) = a := by field_simp [ne_of_gt hμ]
  have hgap : a - μ * (T : ℝ) = μ * u := by rw [hT]; nlinarith
  have ha : μ * (T : ℝ) < a := by nlinarith [mul_pos hμ hu]
  simpa only [hgap] using measure_hitDrift_le_le_exp hB hm hcont hTpos hμ.le ha

/-- A strictly earlier nonpositive time cannot contain a nonnegative hitting time. -/
theorem measure_hitDrift_lt_ofReal_of_nonpos {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (μ a t : ℝ) (ht : t ≤ 0) :
    P {ω | hitDrift B μ a ω < ENNReal.ofReal t} = 0 := by
  rw [ENNReal.ofReal_of_nonpos ht]
  simp

end LatticeProb
