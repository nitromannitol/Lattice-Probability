import LatticeProb.MeasureTheory.BoundedDensityEvaluation
import LatticeProb.MeasureTheory.ContinuousMeasureDurationEndpoints

/-! # Finite kernels from bounded density families -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb

/-- Bounded densities on a finite measure space form a finite kernel when their
integrated truncated discrepancy controls the parameter distance. -/
theorem exists_finite_kernel_of_bounded_density
    {Θ X : Type*} [PseudoMetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    [MeasurableSpace X] (μ : Measure X) (hμ : μ Set.univ < ∞)
    (f : Θ → X → ℝ) (d : Θ → Θ → X → ℝ) (L : ℝ)
    (hf : ∀ θ, Integrable (f θ) μ)
    (hbound : ∀ θ, ∀ᵐ x ∂μ, 0 ≤ f θ x ∧ f θ x ≤ L)
    (hd : ∀ θ η, Integrable (fun x => min 1 (d θ η x)) μ)
    (hpoint : ∀ θ η, ∀ᵐ x ∂μ, |f θ x - f η x| ≤ d θ η x)
    (hcontrol : ∀ θ η, ∫ x, min 1 (d θ η x) ∂μ ≤ dist θ η) :
    ∃ κ : Kernel Θ X, IsFiniteKernel κ ∧
      ∀ θ, κ θ = μ.withDensity (fun x => ENNReal.ofReal (f θ x)) := by
  apply exists_finite_kernel_of_continuous_measure_evaluations
    (fun θ => μ.withDensity (fun x => ENNReal.ofReal (f θ x)))
    (ENNReal.ofReal L * μ Set.univ)
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ
  · intro θ
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ← lintegral_const]
    exact lintegral_mono_ae ((hbound θ).mono fun _ hx => ENNReal.ofReal_le_ofReal hx.2)
  · intro s hs
    exact (lipschitzWith_density_evaluation μ f d L hf hbound hd hpoint hcontrol s hs).continuous

end LatticeProb
