/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import LatticeProb.Prob.CorrelatedBMConeWindowProductSurvival

/-! # Survival bounds for factorial-grid cone events -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- The grid-event estimate with the single-coordinate survival factors bounded. -/
theorem measure_factorialConeGridEvent_one_le_survival {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (C α : ℝ) (k n : ℕ)
    (i j : Fin (n.factorial ^ 6)) (h : ℝ)
    (hh : 0 < h) (hH : h ≤ 1 / (k + 1 : ℝ))
    (hgap : (i.val : ℝ) / (n.factorial ^ 6 : ℕ) + h <
      (j.val : ℝ) / (n.factorial ^ 6 : ℕ) - h)
    (hq : 0 ≤ C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α) :
    let a : ℝ := (i.val : ℝ) / (n.factorial ^ 6 : ℕ)
    let b : ℝ := (j.val : ℝ) / (n.factorial ^ 6 : ℕ)
    let q : ℝ := C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α
    μ (factorialConeGridEvent 1 C α k n i j) ≤
      (ENNReal.ofReal (3 * q / Real.sqrt h) *
        μ ({ω | ∀ t ∈ Icc (b - h) b,
          -q ≤ coneIncr 0 t (b - h) ω - coneIncr 0 b (b - h) ω} ∩
          {ω | ∀ t ∈ Icc (b - h) b,
          -q ≤ coneIncr 1 t (b - h) ω - coneIncr 1 b (b - h) ω}) +
       ENNReal.ofReal (3 * q / Real.sqrt h) *
        μ ({ω | ∀ t ∈ Icc (b - h) b,
          -q ≤ coneIncr 1 t (b - h) ω - coneIncr 1 b (b - h) ω} ∩
          {ω | ∀ t ∈ Icc (b - h) b,
          -q ≤ coneIncr 0 t (b - h) ω - coneIncr 0 b (b - h) ω})) *
        ENNReal.ofReal (2 * q / √(2 * Real.pi * (b - h - (a + h)))) := by
  dsimp only
  apply le_trans (measure_factorialConeGridEvent_one_le hμ C α k n i j h
    (le_of_lt hh) hH hgap hq)
  apply mul_le_mul' ?_ le_rfl
  exact add_le_add
    (coneWindowBarrierProduct_le_survival hμ _ _ 0 1 hh hq)
    (coneWindowBarrierProduct_le_survival hμ _ _ 1 0 hh hq)

/-- The grid-event estimate with the single-coordinate survival factors bounded. -/
theorem measure_factorialConeGridEvent_neg_one_le_survival {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (C α : ℝ) (k n : ℕ)
    (i j : Fin (n.factorial ^ 6)) (h : ℝ)
    (hh : 0 < h) (hH : h ≤ 1 / (k + 1 : ℝ))
    (hgap : (i.val : ℝ) / (n.factorial ^ 6 : ℕ) + h <
      (j.val : ℝ) / (n.factorial ^ 6 : ℕ) - h)
    (hq : 0 ≤ C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α) :
    let a : ℝ := (i.val : ℝ) / (n.factorial ^ 6 : ℕ)
    let b : ℝ := (j.val : ℝ) / (n.factorial ^ 6 : ℕ)
    let q : ℝ := C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α
    μ (factorialConeGridEvent (-1) C α k n i j) ≤
      (ENNReal.ofReal (3 * q / Real.sqrt h) *
        μ ({ω | ∀ t ∈ Icc (-b) (-b + h), -q ≤ coneIncr 0 t (-b) ω} ∩
          {ω | ∀ t ∈ Icc (-b) (-b + h), -q ≤ coneIncr 1 t (-b) ω}) +
       ENNReal.ofReal (3 * q / Real.sqrt h) *
        μ ({ω | ∀ t ∈ Icc (-b) (-b + h), -q ≤ coneIncr 1 t (-b) ω} ∩
          {ω | ∀ t ∈ Icc (-b) (-b + h), -q ≤ coneIncr 0 t (-b) ω})) *
        ENNReal.ofReal (2 * q / √(2 * Real.pi * (b - h - (a + h)))) := by
  dsimp only
  apply le_trans (measure_factorialConeGridEvent_neg_one_le hμ C α k n i j h
    (le_of_lt hh) hH hgap hq)
  apply mul_le_mul' ?_ le_rfl
  exact add_le_add
    (reflectedConeWindowBarrierProduct_le_survival hμ _ _ 0 1 hh hq)
    (reflectedConeWindowBarrierProduct_le_survival hμ _ _ 1 0 hh hq)

end LatticeProb.CorrelatedBM
