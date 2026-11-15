import LatticeProb.MeasureTheory.ExponentialWindowDensityKernel
import LatticeProb.MeasureTheory.MeasurableKernelDurationEndpoints

/-! # Endpoint recovery under exponential-window control -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set

namespace LatticeProb

/-- Exponentially weighted profile control yields a measurable endpoint selector for
interval covers whose lengths are recorded by the profile. -/
theorem exists_measurable_duration_endpoints_of_exponential_discrepancy_control
    {Θ : Type*} [PseudoMetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (T u L C : ℝ) (hC : 0 ≤ C) (f : Θ → ℝ → ℝ) (d : Θ → Θ → ℝ → ℝ)
    (hf : ∀ θ, Integrable (f θ) (volume.restrict (Ioo 0 T)))
    (hbound : ∀ θ, ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), 0 ≤ f θ t ∧ f θ t ≤ L)
    (hd : ∀ θ η, Integrable (fun t => min 1 (d θ η t)) (volume.restrict (Ioo 0 T)))
    (hw : ∀ θ η, Integrable (fun t => Real.exp (-t) * min 1 (d θ η t))
      (volume.restrict (Ioi 0)))
    (hnonneg : ∀ θ η, ∀ᵐ t ∂(volume.restrict (Ioi 0)), 0 ≤ d θ η t)
    (hpoint : ∀ θ η, ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      |f θ t - f η t| ≤ d θ η t)
    (hcontrol : ∀ θ η, ∫ t in Ioi 0, Real.exp (-t) * min 1 (d θ η t)
      ≤ C * dist θ η) :
    ∃ E : Θ → ℝ × ℝ, Measurable E ∧
      ∀ (θ : Θ) {ι : Type*} (A B : ι → ℝ),
        (∀ i, 0 ≤ A i ∧ A i < B i ∧ B i ≤ T) →
        (Pairwise fun i j => Disjoint (Ioo (A i) (B i)) (Ioo (A j) (B j))) →
        volume (Ioo 0 T \ ⋃ i, Ioo (A i) (B i)) = 0 →
        (∀ i, ∀ᵐ t ∂(volume.restrict (Ioo (A i) (B i))), f θ t = B i - A i) →
        ∀ i, u ∈ Ioo (A i) (B i) → E θ = (A i, B i) := by
  obtain ⟨κ, hκ, hκeq⟩ :=
    exists_finite_kernel_of_exponential_discrepancy_control T L C hC f d hf hbound hd hw
      hnonneg hpoint hcontrol
  have : IsFiniteKernel κ := hκ
  obtain ⟨E, hE, hEeq⟩ := exists_measurable_kernel_duration_endpoints 0 u T κ
  refine ⟨E, hE, ?_⟩
  intro θ ι A B hAB hdis hcover hprofile i hi
  exact hEeq θ (f θ) (hf θ).aemeasurable ((hbound θ).mono fun _ h => h.1)
    (hκeq θ) A B hAB hdis hcover hprofile i hi

end LatticeProb
