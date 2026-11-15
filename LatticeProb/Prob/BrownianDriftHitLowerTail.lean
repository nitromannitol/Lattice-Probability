import LatticeProb.Prob.BrownianSupTail
import LatticeProb.Prob.BrownianDriftRestartHit

/-! # Early hitting of a level by Brownian motion with drift -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- Before the deterministic drift reaches the level, an early hit requires
an upward Brownian fluctuation at least as large as the remaining gap. -/
theorem measure_hitDrift_le_le_exp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {μ a : ℝ} {T : ℝ≥0} (hT : 0 < T) (hμ : 0 ≤ μ) (ha : μ * T < a) :
    P {ω | hitDrift B μ a ω ≤ (T : ℝ≥0∞)} ≤
      ENNReal.ofReal (Real.exp (-((a - μ * T) ^ 2 / (2 * T)))) := by
  have hgap : 0 < a - μ * (T : ℝ) := by linarith
  calc
    P {ω | hitDrift B μ a ω ≤ (T : ℝ≥0∞)} ≤
        P {ω | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ a - μ * T ≤ B t ω} := by
      apply measure_mono
      intro ω hω
      obtain ⟨t, ht, hat⟩ := (hitDrift_le_iff hcont μ a ω T).1 hω
      have ht' : (t : ℝ) ≤ T := by exact_mod_cast ht
      have hmul : μ * (t : ℝ) ≤ μ * T := mul_le_mul_of_nonneg_left ht' hμ
      exact ⟨t, ht', by linarith⟩
    _ ≤ ENNReal.ofReal (Real.exp (-((a - μ * T) ^ 2 / (2 * T)))) :=
      measure_exists_le_ge_le_exp hB hm (Filter.Eventually.of_forall hcont)
        (by exact_mod_cast hT) hgap

end LatticeProb
