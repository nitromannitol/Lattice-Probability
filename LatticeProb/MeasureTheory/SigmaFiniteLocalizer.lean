import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Localizers for a σ-finite measure

A σ-finite measure `μ` admits an increasing sequence of measurable functions `0 ≤ h_j ≤ 1` of finite `μ`-integral
such that every point `x` satisfies `h_j x = 1` for all large `j`: the indicators of the spanning sets of `μ`.
Such localizers reduce statements about integrals against a σ-finite measure to statements about finite integrals
by monotone convergence (for instance in the uniqueness theorem for Revuz measures, Fukushima–Oshima–Takeda (2011),
Theorem 5.1.4).
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace LatticeProb

/-- **Localizers for a σ-finite measure.** A σ-finite measure `μ` admits measurable functions `0 ≤ h_j ≤ 1` of
finite `μ`-integral, increasing in `j`, such that every point `x` has `h_j(x) = 1` for all large `j`. -/
theorem exists_localizer_of_sigmaFinite {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] :
    ∃ h : ℕ → α → ℝ≥0∞, (∀ j, Measurable (h j)) ∧ (∀ j x, h j x ≤ 1) ∧
      (∀ j, ∫⁻ x, h j x ∂μ < ∞) ∧ (∀ x, Monotone fun j => h j x) ∧ ∀ x, ∀ᶠ j in atTop, h j x = 1 := by
  refine ⟨fun j => (spanningSets μ j).indicator 1,
    fun j => measurable_one.indicator (measurableSet_spanningSets μ j), fun j x => ?_, fun j => ?_,
    fun x i j hij => ?_, fun x => ?_⟩
  · by_cases hx : x ∈ spanningSets μ j <;> simp [hx]
  · rw [lintegral_indicator_one (measurableSet_spanningSets μ j)]
    exact measure_spanningSets_lt_top μ j
  · exact indicator_le_indicator_of_subset (monotone_spanningSets μ hij) (fun _ => zero_le) x
  · filter_upwards [eventually_ge_atTop (spanningSetsIndex μ x)] with j hj
    exact indicator_of_mem (monotone_spanningSets μ hj (mem_spanningSetsIndex μ x)) _

end LatticeProb
