import LatticeProb.MeasureTheory.MeasurableDensityProfile
import LatticeProb.MeasureTheory.JointProfileReferenceDiscrepancy
import LatticeProb.MeasureTheory.MeasurableProfileReferenceTests

/-! # Scalar observables of finite-kernel density profiles -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace Filter ProbabilityTheory

namespace LatticeProb.MeasurableProfile

/-- A uniformly controlled scalar observable of nonnegative density profiles of a finite
kernel is measurable. Profiles may be chosen independently up to almost-everywhere equality. -/
theorem measurable_scalar_of_finite_kernel_densities
    {Y Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {D : Set ℝ} (hDc : D.Countable) (hD : Dense D)
    {𝒜 : Set (Set ℝ)} (hAc : 𝒜.Countable) (h𝒜 : IsSetAlgebra 𝒜)
    (hA : μ.MeasureDense 𝒜) (V : Set (MeasurableProfile (E := ℝ) μ))
    (hV : V.Nonempty) (q : MeasurableProfile (E := ℝ) μ → Y) (δ : Y → Y → ℝ)
    (hδ : ∀ f ∈ V, ∀ g ∈ V, δ (q f) (q g) ≤ (integralDist μ f g).toReal)
    (z : Ω → Y) (g : Ω → MeasurableProfile (E := ℝ) μ)
    (hgV : ∀ ω, g ω ∈ V) (hgq : ∀ ω, q (g ω) = z ω)
    (κ : Kernel Ω ℝ) [IsFiniteKernel κ]
    (hgpos : ∀ ω, ∀ᵐ t ∂μ, 0 ≤ (g ω).1 t)
    (hgκ : ∀ ω, κ ω = μ.withDensity (fun t => ENNReal.ofReal ((g ω).1 t)))
    (F : Y → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ f ∈ V, ∀ g ∈ V, |F (q g) - F (q f)| ≤ C * δ (q f) (q g)) :
    Measurable (fun ω => F (z ω)) := by
  obtain ⟨G, hG, hGeq⟩ := exists_measurable_real_density_profile μ κ
  let g' : Ω → MeasurableProfile (E := ℝ) μ := fun ω =>
    ⟨fun t => G (ω, t), (hG.comp (measurable_const.prodMk measurable_id)).aemeasurable⟩
  have hgj : Measurable (fun p : Ω × ℝ => (g' p.1).1 p.2) := hG
  have hdist (f : MeasurableProfile (E := ℝ) μ) (ω : Ω) :
      integralDist μ f (g' ω) = integralDist μ f (g ω) := by
    apply lintegral_congr_ae
    filter_upwards [hGeq ω (g ω).1 (g ω).2 (hgpos ω) (hgκ ω)] with t ht
    simp only [g', ht]
  have hm : Measurable (fun ω => F (q (g ω))) := by
    apply measurable_scalar_of_valid_reference_tests μ hDc hD hAc h𝒜 hA V hV
      id (fun f g => (integralDist μ f g).toReal) (by intros; rfl)
      g (fun f => F (q f)) C hC
    · exact fun ω => ⟨g ω, hgV ω, rfl⟩
    · intro f _
      have h := measurable_integralDist_toReal μ f g' hgj
      simpa only [id_eq, hdist] using h
    · intro f hf f' hf'
      exact (hbound f hf f' hf').trans (mul_le_mul_of_nonneg_left (hδ f hf f' hf') hC)
  simpa only [hgq] using hm

end LatticeProb.MeasurableProfile
