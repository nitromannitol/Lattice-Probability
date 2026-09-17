/-
Fubini for a bounded jointly measurable function of two probability spaces.

A bounded jointly measurable function is integrable for the product measure, so
the two iterated integrals agree.  This is the form in which the survival
estimates of the divisible-sandpile paper exchange the order of integration.
-/
import Mathlib

noncomputable section

open MeasureTheory

namespace LatticeProb.Fubini

/-- **Fubini for a bounded jointly measurable function of two probability
spaces.**  If `f` is jointly measurable and bounded by `C`, the two iterated
integrals of `f` agree. -/
theorem integral_integral_swap_of_bounded {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α → β → ℝ) (hf : Measurable (Function.uncurry f)) (C : ℝ)
    (hbd : ∀ a b, |f a b| ≤ C) :
    ∫ a, ∫ b, f a b ∂ν ∂μ = ∫ b, ∫ a, f a b ∂μ ∂ν := by
  have hint : Integrable (Function.uncurry f) (μ.prod ν) := by
    refine Integrable.mono' (integrable_const C) hf.aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_eq_abs]
    exact hbd p.1 p.2
  exact integral_integral_swap hint

end LatticeProb.Fubini
