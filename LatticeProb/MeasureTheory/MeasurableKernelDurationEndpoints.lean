import LatticeProb.MeasureTheory.MeasurableDensityProfile
import LatticeProb.MeasureTheory.MeasurableDurationProfileEndpoints

/-! # Measurable endpoint recovery from density kernels -/

set_option autoImplicit false

open Set MeasureTheory Filter ProbabilityTheory

namespace LatticeProb

/-- A finite kernel determines measurable interval endpoints whenever one of its values
has a nonnegative real density that records the lengths of a disjoint interval cover. -/
theorem exists_measurable_kernel_duration_endpoints
    {Θ : Type*} [MeasurableSpace Θ] (a u b : ℝ)
    (κ : Kernel Θ ℝ) [IsFiniteKernel κ] :
    ∃ E : Θ → ℝ × ℝ, Measurable E ∧
      ∀ (θ : Θ) (f : ℝ → ℝ),
        AEMeasurable f (volume.restrict (Ioo a b)) →
        (∀ᵐ t ∂(volume.restrict (Ioo a b)), 0 ≤ f t) →
        κ θ = (volume.restrict (Ioo a b)).withDensity (fun t => ENNReal.ofReal (f t)) →
        ∀ {ι : Type*} (A B : ι → ℝ),
          (∀ i, a ≤ A i ∧ A i < B i ∧ B i ≤ b) →
          (Pairwise fun i j => Disjoint (Ioo (A i) (B i)) (Ioo (A j) (B j))) →
          volume (Ioo a b \ ⋃ i, Ioo (A i) (B i)) = 0 →
          (∀ i, ∀ᵐ t ∂(volume.restrict (Ioo (A i) (B i))), f t = B i - A i) →
          ∀ i, u ∈ Ioo (A i) (B i) → E θ = (A i, B i) := by
  obtain ⟨F, hF, hFeq⟩ :=
    exists_measurable_real_density_profile (volume.restrict (Ioo a b)) κ
  obtain ⟨E, hE, hEeq⟩ := exists_measurable_duration_profile_endpoints a u b F hF
  refine ⟨E, hE, ?_⟩
  intro θ f hf hpos hκ ι A B hAB hdis hcover hprofile i hi
  apply hEeq θ A B hAB hdis hcover _ i hi
  intro k
  have hsub : Ioo (A k) (B k) ⊆ Ioo a b :=
    Ioo_subset_Ioo (hAB k).1 (hAB k).2.2
  have heq := ae_mono (Measure.restrict_mono hsub le_rfl) (hFeq θ f hf hpos hκ)
  filter_upwards [heq, hprofile k] with t ht ht'
  exact ht.trans ht'

end LatticeProb
