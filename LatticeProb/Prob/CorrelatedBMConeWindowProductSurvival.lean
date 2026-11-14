/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import LatticeProb.Prob.CorrelatedBMConeGridUnionBound
import LatticeProb.Prob.CorrelatedBMReflectedConeGridUnionBound
import LatticeProb.Prob.CorrelatedBMWindowSurvival

/-! # Survival factors in cone-window bounds

The single-coordinate factor in either time orientation has the usual
Brownian survival upper bound. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- Bound the forward product while retaining its joint backward barrier. -/
theorem coneWindowBarrierProduct_le_survival {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (a b : ℝ) {h q : ℝ} (i j : Fin 2)
    (hh : 0 < h) (hq : 0 ≤ q) :
    coneWindowBarrierProduct μ a b h q i j ≤
      ENNReal.ofReal (3 * q / Real.sqrt h) *
        μ ({ω | ∀ t ∈ Icc (b - h) b,
          -q ≤ coneIncr i t (b - h) ω - coneIncr i b (b - h) ω} ∩
          {ω | ∀ t ∈ Icc (b - h) b,
          -q ≤ coneIncr j t (b - h) ω - coneIncr j b (b - h) ω}) := by
  unfold coneWindowBarrierProduct
  exact mul_le_mul' (measure_forward_window_survival_le hμ i a hh hq) le_rfl

/-- Bound the reflected product while retaining its joint forward barrier. -/
theorem reflectedConeWindowBarrierProduct_le_survival {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (a b : ℝ) {h q : ℝ} (i j : Fin 2)
    (hh : 0 < h) (hq : 0 ≤ q) :
    reflectedConeWindowBarrierProduct μ a b h q i j ≤
      ENNReal.ofReal (3 * q / Real.sqrt h) *
        μ ({ω | ∀ t ∈ Icc (-b) (-b + h), -q ≤ coneIncr i t (-b) ω} ∩
          {ω | ∀ t ∈ Icc (-b) (-b + h), -q ≤ coneIncr j t (-b) ω}) := by
  unfold reflectedConeWindowBarrierProduct
  apply mul_le_mul' ?_ le_rfl
  have heq : {ω : Path2 | ∀ t ∈ Icc (-a - h) (-a),
      -q ≤ coneIncr i t (-a - h) ω - coneIncr i (-a) (-a - h) ω} =
      {ω : Path2 | ∀ t ∈ Icc (-a - h) (-a), -q ≤ coneIncr i t (-a) ω} := by
    ext ω
    simp only [mem_ofPred_eq, coneIncr]
    constructor <;> intro hw t ht <;> have ht' := hw t ht <;> linarith
  rw [heq]
  exact measure_backward_window_survival_le hμ i (-a) hh hq

end LatticeProb.CorrelatedBM
