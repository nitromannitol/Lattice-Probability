/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import LatticeProb.Prob.CorrelatedBMConeGridWindowBound
import LatticeProb.Prob.CorrelatedBMConeGridEvents

/-! # A window bound for factorial-grid cone events

The two coordinate orientations are controlled by their respective local
barrier probabilities and a common Gaussian middle-window factor. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- Product of the forward one-coordinate and backward two-coordinate barrier
probabilities on the two outer windows. -/
noncomputable def coneWindowBarrierProduct (μ : Measure Path2) (a b h q : ℝ)
    (i j : Fin 2) : ℝ≥0∞ :=
  μ {ω | ∀ t ∈ Icc a (a + h), -q ≤ coneIncr i t a ω} *
    μ ({ω | ∀ t ∈ Icc (b - h) b,
      -q ≤ coneIncr i t (b - h) ω - coneIncr i b (b - h) ω} ∩
      {ω | ∀ t ∈ Icc (b - h) b,
      -q ≤ coneIncr j t (b - h) ω - coneIncr j b (b - h) ω})

/-- The factorial-grid union is bounded by the two orientation estimates. -/
theorem measure_factorialConeGridEvent_one_le {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (C α : ℝ) (k n : ℕ)
    (i j : Fin (n.factorial ^ 6)) (h : ℝ)
    (hh : 0 ≤ h) (hH : h ≤ 1 / (k + 1 : ℝ))
    (hgap : (i.val : ℝ) / (n.factorial ^ 6 : ℕ) + h <
      (j.val : ℝ) / (n.factorial ^ 6 : ℕ) - h)
    (hq : 0 ≤ C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α) :
    let a : ℝ := (i.val : ℝ) / (n.factorial ^ 6 : ℕ)
    let b : ℝ := (j.val : ℝ) / (n.factorial ^ 6 : ℕ)
    let q : ℝ := C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α
    μ (factorialConeGridEvent 1 C α k n i j) ≤
      (coneWindowBarrierProduct μ a b h q 0 1 +
        coneWindowBarrierProduct μ a b h q 1 0) *
        ENNReal.ofReal (2 * q / √(2 * Real.pi * (b - h - (a + h)))) := by
  dsimp only
  have h₀ := measure_approximateConeGridEvent_le hμ
    ((i.val : ℝ) / (n.factorial ^ 6 : ℕ))
    ((j.val : ℝ) / (n.factorial ^ 6 : ℕ)) h (1 / (k + 1 : ℝ))
    (C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α) 0 1 hh hH hgap hq
  have h₁ := measure_approximateConeGridEvent_le hμ
    ((i.val : ℝ) / (n.factorial ^ 6 : ℕ))
    ((j.val : ℝ) / (n.factorial ^ 6 : ℕ)) h (1 / (k + 1 : ℝ))
    (C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α) 1 0 hh hH hgap hq
  calc
    μ (factorialConeGridEvent 1 C α k n i j) ≤
        μ (approximateConeGridEvent (fun ω t => lrCoord 0 t ω)
          (fun ω t => lrCoord 1 t ω)
          (fun _ => C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α)
          ((i.val : ℝ) / (n.factorial ^ 6 : ℕ))
          ((j.val : ℝ) / (n.factorial ^ 6 : ℕ)) (1 / (k + 1 : ℝ))) +
        μ (approximateConeGridEvent (fun ω t => lrCoord 1 t ω)
          (fun ω t => lrCoord 0 t ω)
          (fun _ => C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α)
          ((i.val : ℝ) / (n.factorial ^ 6 : ℕ))
          ((j.val : ℝ) / (n.factorial ^ 6 : ℕ)) (1 / (k + 1 : ℝ))) := by
      simpa only [factorialConeGridEvent, one_mul] using
        measure_union_le (μ := μ)
          (approximateConeGridEvent (fun ω t => lrCoord 0 t ω)
            (fun ω t => lrCoord 1 t ω)
            (fun _ => C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α)
            ((i.val : ℝ) / (n.factorial ^ 6 : ℕ))
            ((j.val : ℝ) / (n.factorial ^ 6 : ℕ)) (1 / (k + 1 : ℝ)))
          (approximateConeGridEvent (fun ω t => lrCoord 1 t ω)
            (fun ω t => lrCoord 0 t ω)
            (fun _ => C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α)
            ((i.val : ℝ) / (n.factorial ^ 6 : ℕ))
            ((j.val : ℝ) / (n.factorial ^ 6 : ℕ)) (1 / (k + 1 : ℝ)))
    _ ≤ _ := by
      simpa only [coneWindowBarrierProduct, add_mul] using add_le_add h₀ h₁

end LatticeProb.CorrelatedBM
