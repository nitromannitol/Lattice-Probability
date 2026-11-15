import LatticeProb.Prob.CorrelatedBMUnitPowerDimension
import LatticeProb.Prob.CorrelatedBMWindowSurvival

/-! # A universal dimension bound for direct-excursion pairs -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MesoModel

namespace LatticeProb.CorrelatedBM

/-- A joint barrier is bounded by the corresponding one-coordinate barrier. -/
theorem measure_jointZeroBarrier_le_one_coordinate {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) {q h : ℝ} (hq : 0 ≤ q) (hh : 0 < h) :
    μ (jointZeroBarrier q h) ≤ ENNReal.ofReal (3 * q / Real.sqrt h) := by
  calc
    μ (jointZeroBarrier q h) ≤
        μ {ω | ∀ t ∈ Icc 0 (0 + h), -q ≤ coneIncr 0 t 0 ω} := by
      apply measure_mono
      intro ω hω
      simpa only [zero_add] using hω.1
    _ ≤ ENNReal.ofReal (3 * q / Real.sqrt h) :=
      measure_forward_window_survival_le hμ 0 0 hh hq

/-- The direct-excursion pair set has Hausdorff dimension at most one half. -/
theorem ae_dimH_direct_excursion_pairs_le_half
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, dimH {q : ℝ × ℝ | ∃ a b, a ≠ b ∧
      ((DirectRel (lrCoord 0 · ω) q.1 a ∧ DirectRel (lrCoord 1 · ω) q.1 b) ∨
       (DirectRel (lrCoord 0 · ω) a q.1 ∧ DirectRel (lrCoord 1 · ω) b q.1)) ∧
      (q.2 = a ∨ q.2 = b)} ≤ (1 / 2 : ℝ≥0) := by
  apply ae_dimH_direct_excursion_pairs_le_of_unit_power hμ (1 / 2) 3 1
    (by norm_num) (by norm_num)
  intro q hq ν hν
  simpa only [Real.rpow_one, Real.sqrt_one, div_one] using
    (measure_jointZeroBarrier_le_one_coordinate hν hq.le (show (0 : ℝ) < 1 by norm_num))

end LatticeProb.CorrelatedBM
