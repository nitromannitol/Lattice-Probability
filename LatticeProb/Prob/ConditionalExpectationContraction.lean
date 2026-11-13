import Mathlib
import LatticeProb.Prob.ConditionalLawCriterion

/-!
# Contraction of conditional expectations in `L¹` towards coarser measurable functions

Let `m₁ ≤ m₂` be sub-σ-algebras and `B` an integrable `m₁`-measurable function.  Since
`E[g | m₁] - B = E[E[g | m₂] - B | m₁]`, the `L¹` distance of `E[g | m₁]` to `B` is at most the `L¹`
distance of `E[g | m₂]` to `B`.

* `LatticeProb.integral_abs_condExp_sub_le_of_le`: this contraction.
* `LatticeProb.integral_abs_condExpGiven_sub_le`: the case `m₁ = σ(Y)`, `B = b ∘ Y`: the `L¹` error of
  `E[f (X) | Y]` against a function `b (Y)` of the conditioning variable is at most the `L¹` error of the
  conditional expectation given any finer σ-algebra (for instance the σ-algebra of the past of a Markov
  chain together with its environment, where the conditional expectation is a quenched kernel).
-/

set_option autoImplicit false

open MeasureTheory MeasurableSpace

namespace LatticeProb

/-- **Contraction of the conditional expectation.**  For sub-σ-algebras `m₁ ≤ m₂`, a function `g` and
an integrable `m₁`-measurable `B`, the `L¹` distance from `E[g | m₁]` to `B` is at most the `L¹` distance
from `E[g | m₂]` to `B`. -/
theorem integral_abs_condExp_sub_le_of_le {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {m₁ m₂ : MeasurableSpace Ω} (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀)
    {g B : Ω → ℝ} (hB : StronglyMeasurable[m₁] B) (hBi : Integrable B μ) :
    ∫ ω, |μ[g | m₁] ω - B ω| ∂μ ≤ ∫ ω, |μ[g | m₂] ω - B ω| ∂μ := by
  have hm₁ : m₁ ≤ m₀ := hm₁₂.trans hm₂
  have h1 : μ[μ[g | m₂] | m₁] =ᵐ[μ] μ[g | m₁] := condExp_condExp_of_le hm₁₂ hm₂
  have h2 : μ[B | m₁] = B := condExp_of_stronglyMeasurable hm₁ hB hBi
  have h3 : μ[μ[g | m₂] - B | m₁] =ᵐ[μ] μ[μ[g | m₂] | m₁] - μ[B | m₁] :=
    condExp_sub integrable_condExp hBi m₁
  have h4 : ∀ᵐ ω ∂μ, |μ[g | m₁] ω - B ω| = |μ[μ[g | m₂] - B | m₁] ω| := by
    filter_upwards [h1, h3] with ω a c
    rw [c, h2]
    simp [a]
  calc ∫ ω, |μ[g | m₁] ω - B ω| ∂μ = ∫ ω, |μ[μ[g | m₂] - B | m₁] ω| ∂μ := integral_congr_ae h4
    _ ≤ ∫ ω, |μ[g | m₂] ω - B ω| ∂μ := integral_abs_condExp_le (μ[g | m₂] - B)

/-- **Contraction for conditional laws.**  If `σ(Y) ≤ G` and `b` is measurable with `b (Y)` integrable,
then the `L¹` distance of `E[f (X) | Y]` to `b (Y)` is at most the `L¹` distance of `E[f (X) | G]` to
`b (Y)`. -/
theorem integral_abs_condExpGiven_sub_le {Ω E F : Type*} {G m₀ : MeasurableSpace Ω}
    [MeasurableSpace E] [MeasurableSpace F] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : Ω → E) (Y : Ω → F) (f : E → ℝ)
    (hYG : MeasurableSpace.comap Y inferInstance ≤ G) (hG : G ≤ m₀)
    {b : F → ℝ} (hb : Measurable b) (hbi : Integrable (fun ω => b (Y ω)) μ) :
    ∫ ω, |condExpGiven μ X Y f ω - b (Y ω)| ∂μ ≤
      ∫ ω, |μ[fun ω => f (X ω) | G] ω - b (Y ω)| ∂μ :=
  integral_abs_condExp_sub_le_of_le hYG hG
    (hb.comp (comap_measurable Y)).stronglyMeasurable hbi

end LatticeProb
