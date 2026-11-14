/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import LatticeProb.Prob.CorrelatedBMRationalDescent
import LatticeProb.Prob.BrownianSurvivalUpper
import LatticeProb.Prob.CorrelatedBMConeTimes

/-! # Single-coordinate survival on Brownian windows

The forward and backward increments of either coordinate have the usual
one-dimensional Brownian survival upper bound. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- A forward window has the standard Brownian survival bound. -/
theorem measure_forward_window_survival_le {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) (a : ℝ) {h q : ℝ}
    (hh : 0 < h) (hq : 0 ≤ q) :
    μ {ω | ∀ t ∈ Icc a (a + h), -q ≤ coneIncr i t a ω} ≤
      ENNReal.ofReal (3 * q / Real.sqrt h) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hT : (0 : ℝ≥0) < h.toNNReal := Real.toNNReal_pos.2 hh
  calc
    μ {ω | ∀ t ∈ Icc a (a + h), -q ≤ coneIncr i t a ω} ≤
        μ {ω | ∀ s ≤ h.toNNReal,
          -q ≤ shiftedCoordinate i a s ω - shiftedCoordinate i a 0 ω} := by
      apply measure_mono
      intro ω hω s hs
      have hs' : (s : ℝ) ≤ h := by
        have h' := NNReal.coe_le_coe.2 hs
        rwa [Real.coe_toNNReal _ hh.le] at h'
      have ht := hω (a + (s : ℝ)) ⟨by linarith [NNReal.coe_nonneg s], by linarith⟩
      simpa [shiftedCoordinate, coneIncr] using ht
    _ ≤ ENNReal.ofReal (3 * q / Real.sqrt (h.toNNReal : ℝ)) :=
      measure_forall_ge_neg_le (shiftedCoordinate_isBrownianReal hμ i a)
        (fun t => (measurable_lrCoord (i, _)).sub (measurable_lrCoord (i, _))) hT hq
    _ = ENNReal.ofReal (3 * q / Real.sqrt h) := by rw [Real.coe_toNNReal _ hh.le]

/-- A backward window has the standard Brownian survival bound. -/
theorem measure_backward_window_survival_le {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) (a : ℝ) {h q : ℝ}
    (hh : 0 < h) (hq : 0 ≤ q) :
    μ {ω | ∀ t ∈ Icc (a - h) a, -q ≤ coneIncr i t a ω} ≤
      ENNReal.ofReal (3 * q / Real.sqrt h) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hT : (0 : ℝ≥0) < h.toNNReal := Real.toNNReal_pos.2 hh
  calc
    μ {ω | ∀ t ∈ Icc (a - h) a, -q ≤ coneIncr i t a ω} ≤
        μ {ω | ∀ s ≤ h.toNNReal,
          -q ≤ reversedCoordinate i a s ω - reversedCoordinate i a 0 ω} := by
      apply measure_mono
      intro ω hω s hs
      have hs' : (s : ℝ) ≤ h := by
        have h' := NNReal.coe_le_coe.2 hs
        rwa [Real.coe_toNNReal _ hh.le] at h'
      have ht := hω (a - (s : ℝ)) ⟨by linarith, by linarith [NNReal.coe_nonneg s]⟩
      simpa [reversedCoordinate, coneIncr] using ht
    _ ≤ ENNReal.ofReal (3 * q / Real.sqrt (h.toNNReal : ℝ)) :=
      measure_forall_ge_neg_le (reversedCoordinate_isBrownianReal hμ i a)
        (fun t => (measurable_lrCoord (i, _)).sub (measurable_lrCoord (i, _))) hT hq
    _ = ENNReal.ofReal (3 * q / Real.sqrt h) := by rw [Real.coe_toNNReal _ hh.le]

end LatticeProb.CorrelatedBM
