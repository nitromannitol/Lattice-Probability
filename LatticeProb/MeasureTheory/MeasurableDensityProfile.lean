import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! # Measurable representatives of density profiles -/

set_option autoImplicit false

open MeasureTheory Filter
open ProbabilityTheory

namespace LatticeProb

/-- A finite kernel has a jointly measurable real density representative. Whenever a
kernel value is represented by a nonnegative almost-everywhere measurable real density,
the representative agrees with that density almost everywhere. -/
theorem exists_measurable_real_density_profile
    {Θ : Type*} [MeasurableSpace Θ] (μ : Measure ℝ) [IsFiniteMeasure μ]
    (κ : Kernel Θ ℝ) [IsFiniteKernel κ] :
    ∃ F : Θ × ℝ → ℝ, Measurable F ∧
      ∀ (θ : Θ) (f : ℝ → ℝ), AEMeasurable f μ →
        (∀ᵐ t ∂μ, 0 ≤ f t) →
        κ θ = μ.withDensity (fun t => ENNReal.ofReal (f t)) →
        ∀ᵐ t ∂μ, F (θ, t) = f t := by
  let η : Kernel Θ ℝ := Kernel.const Θ μ
  refine ⟨fun p => (κ.rnDeriv η p.1 p.2).toReal,
    (Kernel.measurable_rnDeriv κ η).ennreal_toReal, ?_⟩
  intro θ f hf hpos hκ
  have h₁ := Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := θ)
  have h₂ := Measure.rnDeriv_withDensity₀ μ hf.ennreal_ofReal
  change (κ.rnDeriv η θ) =ᵐ[μ] (κ θ).rnDeriv μ at h₁
  rw [hκ] at h₁
  filter_upwards [h₁, h₂, hpos] with t ht ht' hnonneg
  rw [ht, ht', ENNReal.toReal_ofReal hnonneg]

end LatticeProb
