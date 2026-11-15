import LatticeProb.MeasureTheory.MeasurableKernelDurationEndpoints

/-! # Endpoint recovery from continuously varying measure evaluations -/

set_option autoImplicit false

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb

/-- Uniformly finite measures with continuous evaluations form a finite kernel. -/
theorem exists_finite_kernel_of_continuous_measure_evaluations
    {Θ X : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    [MeasurableSpace X] (M : Θ → Measure X) (C : ℝ≥0∞)
    (hC : C < ∞) (hbound : ∀ θ, M θ univ ≤ C)
    (hcont : ∀ s, MeasurableSet s → Continuous (fun θ => (M θ s).toReal)) :
    ∃ κ : Kernel Θ X, IsFiniteKernel κ ∧ ∀ θ, κ θ = M θ := by
  have hfinite (θ : Θ) (s : Set X) : M θ s ≠ ∞ :=
    (lt_of_le_of_lt ((measure_mono (subset_univ s)).trans (hbound θ)) hC).ne
  have hmeas : Measurable M := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have h := ENNReal.measurable_ofReal.comp (hcont s hs).measurable
    convert h using 1
    funext θ
    exact (ENNReal.ofReal_toReal (hfinite θ s)).symm
  refine ⟨⟨M, hmeas⟩, ⟨⟨C, hC, hbound⟩⟩, ?_⟩
  intro θ
  rfl

/-- Continuously varying finite-measure evaluations admit measurable duration endpoint
recovery whenever the explicit density and interval-cover hypotheses hold. -/
theorem exists_measurable_duration_endpoints_of_continuous_measure_evaluations
    {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (a u b : ℝ) (M : Θ → Measure ℝ) (C : ℝ≥0∞)
    (hC : C < ∞) (hbound : ∀ θ, M θ univ ≤ C)
    (hcont : ∀ s, MeasurableSet s → Continuous (fun θ => (M θ s).toReal)) :
    ∃ E : Θ → ℝ × ℝ, Measurable E ∧
      ∀ (θ : Θ) (f : ℝ → ℝ),
        AEMeasurable f (volume.restrict (Ioo a b)) →
        (∀ᵐ t ∂(volume.restrict (Ioo a b)), 0 ≤ f t) →
        M θ = (volume.restrict (Ioo a b)).withDensity (fun t => ENNReal.ofReal (f t)) →
        ∀ {ι : Type*} (A B : ι → ℝ),
          (∀ i, a ≤ A i ∧ A i < B i ∧ B i ≤ b) →
          (Pairwise fun i j => Disjoint (Ioo (A i) (B i)) (Ioo (A j) (B j))) →
          volume (Ioo a b \ ⋃ i, Ioo (A i) (B i)) = 0 →
          (∀ i, ∀ᵐ t ∂(volume.restrict (Ioo (A i) (B i))), f t = B i - A i) →
          ∀ i, u ∈ Ioo (A i) (B i) → E θ = (A i, B i) := by
  obtain ⟨κ, hκ, hκeq⟩ :=
    exists_finite_kernel_of_continuous_measure_evaluations M C hC hbound hcont
  have : IsFiniteKernel κ := hκ
  obtain ⟨E, hE, hEeq⟩ := exists_measurable_kernel_duration_endpoints a u b κ
  refine ⟨E, hE, ?_⟩
  intro θ f hf hpos hM ι A B hAB hdis hcover hprofile i hi
  exact hEeq θ f hf hpos ((hκeq θ).trans hM) A B hAB hdis hcover hprofile i hi

end LatticeProb
