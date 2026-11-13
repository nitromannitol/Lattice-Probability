import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Second moment of an average of a random process

Let `μ` be a probability measure on a parameter space and let `X v` be real random variables,
jointly measurable in the parameter `v` and the sample `ω`. Then the average `∫ X v dμ(v)` has
second moment at most the average of the second moments:

`E[(∫ X v dμ(v))²] ≤ ∫ E[(X v)²] dμ(v)`.

This is Jensen's inequality `(∫ f dμ)² ≤ ∫ f² dμ` for the probability measure `μ`, applied for each
sample, followed by Tonelli's theorem. Both are stated with `[0, ∞]`-valued lower Lebesgue
integrals, so that no integrability hypothesis is needed (a non-integrable average is `0` by the
convention of the Bochner integral). A typical use is the variance of a mollified Gaussian field
written as an average of circle-average increments over scales against a radial probability
density: the variance is at most the average of the variances of the increments.

* `ofReal_sq_integral_le_lintegral`: `(∫ f dμ)² ≤ ∫⁻ f² dμ` for a probability measure `μ`;
* `lintegral_sq_integral_le`: the second-moment bound for an average of a jointly measurable
  process.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace LatticeProb.WeightedAverageSecondMoment

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma ofReal_sq_eq_enorm_rpow (y : ℝ) : ENNReal.ofReal (y ^ 2) = ‖y‖ₑ ^ (2 : ℝ) := by
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg y) (by norm_num),
    Real.rpow_two, sq_abs]

/-- **Jensen's inequality for the square**, with no integrability hypothesis: for a probability
measure `μ` and any `f : α → ℝ`, `(∫ f dμ)² ≤ ∫⁻ f² dμ`. -/
theorem ofReal_sq_integral_le_lintegral {μ : Measure α} [IsProbabilityMeasure μ] (f : α → ℝ) :
    ENNReal.ofReal ((∫ x, f x ∂μ) ^ 2) ≤ ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ := by
  by_cases hf : AEStronglyMeasurable f μ
  swap
  · rw [integral_undef fun hi => hf hi.aestronglyMeasurable]
    simp
  have h1 : ‖∫ x, f x ∂μ‖ₑ ≤ eLpNorm f ((2 : ℝ≥0) : ℝ≥0∞) μ := by
    refine (enorm_integral_le_lintegral_enorm f).trans ?_
    rw [← eLpNorm_one_eq_lintegral_enorm]
    · exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
    · exact hf
  have h2 := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 2) two_ne_zero hf
  rw [ofReal_sq_eq_enorm_rpow]
  simp_rw [ofReal_sq_eq_enorm_rpow]
  calc ‖∫ x, f x ∂μ‖ₑ ^ (2 : ℝ) ≤ eLpNorm f ((2 : ℝ≥0) : ℝ≥0∞) μ ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow h1 (by norm_num)
    _ = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by simpa using h2

/-- **Second moment of an average of a process.** For a probability measure `μ` on the parameter
space and a jointly measurable real process `X`, the average `ω ↦ ∫ X v ω dμ(v)` satisfies
`E[(∫ X v dμ(v))²] ≤ ∫ E[(X v)²] dμ(v)`. -/
theorem lintegral_sq_integral_le {μ : Measure α} [IsProbabilityMeasure μ] {P : Measure β}
    [SFinite P] (X : α → β → ℝ) (hX : Measurable (Function.uncurry X)) :
    ∫⁻ ω, ENNReal.ofReal ((∫ v, X v ω ∂μ) ^ 2) ∂P ≤
      ∫⁻ v, ∫⁻ ω, ENNReal.ofReal (X v ω ^ 2) ∂P ∂μ := by
  have hm : Measurable (Function.uncurry fun (ω : β) (v : α) => ENNReal.ofReal (X v ω ^ 2)) :=
    ((hX.comp measurable_swap).pow_const 2).ennreal_ofReal
  calc ∫⁻ ω, ENNReal.ofReal ((∫ v, X v ω ∂μ) ^ 2) ∂P
      ≤ ∫⁻ ω, ∫⁻ v, ENNReal.ofReal (X v ω ^ 2) ∂μ ∂P :=
        lintegral_mono fun ω => ofReal_sq_integral_le_lintegral (fun v => X v ω)
    _ = ∫⁻ v, ∫⁻ ω, ENNReal.ofReal (X v ω ^ 2) ∂P ∂μ :=
        lintegral_lintegral_swap hm.aemeasurable

end LatticeProb.WeightedAverageSecondMoment
