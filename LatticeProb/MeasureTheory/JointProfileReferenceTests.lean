import LatticeProb.MeasureTheory.JointProfileReferenceDiscrepancy
import LatticeProb.MeasureTheory.MeasurableProfileReferenceTests
import LatticeProb.MeasureTheory.MeasurableProfileReferenceKernelTests

/-! # Measurability from jointly measurable profile representatives -/

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace LatticeProb.MeasurableProfile

/-- A jointly measurable valid lift supplies the reference tests for a scalar observable. -/
theorem measurable_scalar_of_joint_valid_lift
    {α E Y Ω : Type*} [MeasurableSpace α] [PseudoEMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    (μ : Measure α) [IsFiniteMeasure μ]
    {D : Set E} (hDc : D.Countable) (hD : Dense D)
    {𝒜 : Set (Set α)} (hAc : 𝒜.Countable) (h𝒜 : IsSetAlgebra 𝒜)
    (hA : μ.MeasureDense 𝒜) (V : Set (MeasurableProfile (E := E) μ))
    (hV : V.Nonempty) (q : MeasurableProfile (E := E) μ → Y) (δ : Y → Y → ℝ)
    (hδ : ∀ f ∈ V, ∀ g ∈ V, δ (q f) (q g) ≤ (integralDist μ f g).toReal)
    (z : Ω → Y) (g : Ω → MeasurableProfile (E := E) μ)
    (hgV : ∀ ω, g ω ∈ V) (hgq : ∀ ω, q (g ω) = z ω)
    (hg : Measurable (fun p : Ω × α => (g p.1).1 p.2))
    (F : Y → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ f ∈ V, ∀ g ∈ V, |F (q g) - F (q f)| ≤ C * δ (q f) (q g)) :
    Measurable (fun ω => F (z ω)) := by
  have hm : Measurable (fun ω => F (q (g ω))) := by
    apply measurable_scalar_of_valid_reference_tests μ hDc hD hAc h𝒜 hA V hV
      id (fun f g => (integralDist μ f g).toReal) (by intros; rfl)
      g (fun f => F (q f)) C hC
    · exact fun ω => ⟨g ω, hgV ω, rfl⟩
    · intro f _
      exact measurable_integralDist_toReal μ f g hg
    · intro f hf f' hf'
      exact (hbound f hf f' hf').trans (mul_le_mul_of_nonneg_left (hδ f hf f' hf') hC)
  simpa only [hgq] using hm

/-- A jointly measurable valid lift supplies the reference tests for a finite kernel. -/
theorem exists_finite_kernel_of_joint_valid_lift
    {α E Y Ω X : Type*} [MeasurableSpace α] [PseudoEMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    [MeasurableSpace X]
    (μ : Measure α) [IsFiniteMeasure μ]
    {D : Set E} (hDc : D.Countable) (hD : Dense D)
    {𝒜 : Set (Set α)} (hAc : 𝒜.Countable) (h𝒜 : IsSetAlgebra 𝒜)
    (hA : μ.MeasureDense 𝒜) (V : Set (MeasurableProfile (E := E) μ))
    (hV : V.Nonempty) (q : MeasurableProfile (E := E) μ → Y) (δ : Y → Y → ℝ)
    (hδ : ∀ f ∈ V, ∀ g ∈ V, δ (q f) (q g) ≤ (integralDist μ f g).toReal)
    (z : Ω → Y) (g : Ω → MeasurableProfile (E := E) μ)
    (hgV : ∀ ω, g ω ∈ V) (hgq : ∀ ω, q (g ω) = z ω)
    (hg : Measurable (fun p : Ω × α => (g p.1).1 p.2))
    (M : Y → Measure X) (K : ℝ≥0∞) (hK : K < ∞)
    (hfinite : ∀ ω, M (z ω) univ ≤ K) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ s, MeasurableSet s → ∀ f ∈ V, ∀ g ∈ V,
      |(M (q g) s).toReal - (M (q f) s).toReal| ≤ C * δ (q f) (q g)) :
    ∃ κ : ProbabilityTheory.Kernel Ω X, ProbabilityTheory.IsFiniteKernel κ ∧
      ∀ ω, κ ω = M (z ω) := by
  have hf : ∀ ω, M (q (g ω)) univ ≤ K := by simpa only [hgq] using hfinite
  obtain ⟨κ, hκ, hκeq⟩ := exists_finite_kernel_of_valid_reference_tests μ hDc hD hAc h𝒜 hA
    V hV id (fun f g => (integralDist μ f g).toReal) (by intros; rfl)
    g (fun f => M (q f)) K hK hf C hC (fun ω => ⟨g ω, hgV ω, rfl⟩)
    (fun f _ => measurable_integralDist_toReal μ f g hg)
    (fun s hs f hf f' hf' =>
      (hbound s hs f hf f' hf').trans (mul_le_mul_of_nonneg_left (hδ f hf f' hf') hC))
  exact ⟨κ, hκ, fun ω => (hκeq ω).trans (congrArg M (hgq ω))⟩

end LatticeProb.MeasurableProfile
