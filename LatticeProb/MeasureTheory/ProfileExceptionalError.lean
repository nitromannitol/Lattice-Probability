import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.EMetricSpace.Basic

/-! # Truncated profile error outside an exceptional set -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

/-- Uniform distance control away from an exceptional set bounds the integrated
truncated distance by the uniform error and the measure of the exceptional set. -/
theorem lintegral_min_edist_le_of_forall_not_mem {α E : Type*} [MeasurableSpace α]
    [PseudoEMetricSpace E] (μ : Measure α) (f g : α → E) (B : Set α)
    (δ : ℝ≥0∞) (h : ∀ x ∉ B, edist (f x) (g x) ≤ δ) :
    (∫⁻ x, min 1 (edist (f x) (g x)) ∂μ) ≤ δ * μ univ + μ B := by
  classical
  calc
    (∫⁻ x, min 1 (edist (f x) (g x)) ∂μ) ≤
        ∫⁻ x, δ + B.indicator 1 x ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ B
      · simp only [indicator_of_mem hx, Pi.one_apply]
        exact (min_le_left _ _).trans (le_add_left le_rfl)
      · simp only [indicator_of_notMem hx, add_zero]
        exact (min_le_right _ _).trans (h x hx)
    _ = δ * μ univ + ∫⁻ x, B.indicator 1 x ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_const]
    _ ≤ δ * μ univ + μ B := add_le_add_right (lintegral_indicator_one_le (μ := μ) B) _

end LatticeProb
