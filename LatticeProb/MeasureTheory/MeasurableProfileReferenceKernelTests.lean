import LatticeProb.MeasureTheory.MeasurableProfileValidReferenceCover
import LatticeProb.MeasureTheory.CountableReferenceMeasurability

/-! # Finite kernels from valid profile reference tests -/

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace LatticeProb.MeasurableProfile

/-- Measurable discrepancy tests and uniform evaluation bounds yield a finite kernel
on values represented by valid measurable profiles. -/
theorem exists_finite_kernel_of_valid_reference_tests
    {α E Y Ω X : Type*} [MeasurableSpace α] [PseudoEMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    [MeasurableSpace X]
    (μ : Measure α) [IsFiniteMeasure μ]
    {D : Set E} (hDc : D.Countable) (hD : Dense D)
    {𝒜 : Set (Set α)} (hAc : 𝒜.Countable) (h𝒜 : IsSetAlgebra 𝒜)
    (hA : μ.MeasureDense 𝒜) (V : Set (MeasurableProfile (E := E) μ))
    (hV : V.Nonempty) (q : MeasurableProfile (E := E) μ → Y) (δ : Y → Y → ℝ)
    (hδ : ∀ f ∈ V, ∀ g ∈ V, δ (q f) (q g) ≤ (integralDist μ f g).toReal)
    (z : Ω → Y) (M : Y → Measure X) (K : ℝ≥0∞) (hK : K < ∞)
    (hfinite : ∀ ω, M (z ω) univ ≤ K) (C : ℝ) (hC : 0 ≤ C)
    (hz : ∀ ω, ∃ g ∈ V, q g = z ω)
    (htest : ∀ f ∈ V, Measurable fun ω => δ (q f) (z ω))
    (hbound : ∀ s, MeasurableSet s → ∀ f ∈ V, ∀ g ∈ V,
      |(M (q g) s).toReal - (M (q f) s).toReal| ≤ C * δ (q f) (q g)) :
    ∃ κ : ProbabilityTheory.Kernel Ω X, ProbabilityTheory.IsFiniteKernel κ ∧
      ∀ ω, κ ω = M (z ω) := by
  obtain ⟨_, r, hr, hcover⟩ :=
    separableSpace_and_exists_countable_valid_reference_cover μ hDc hD hAc h𝒜 hA V hV q δ hδ
  apply LatticeProb.exists_finite_kernel_of_countable_reference_discrepancies
    (fun ω => M (z ω)) (fun n => M (q (r n))) K hK hfinite
    (fun n ω => δ (q (r n)) (z ω)) C hC
  · exact fun n => htest (r n) (hr n)
  · intro s hs n ω
    obtain ⟨g, hg, hq⟩ := hz ω
    rw [← hq]
    exact hbound s hs (r n) (hr n) g hg
  · intro ω ε hε
    obtain ⟨g, hg, hq⟩ := hz ω
    obtain ⟨n, hn⟩ := hcover g hg ε hε
    exact ⟨n, hq ▸ hn⟩

end LatticeProb.MeasurableProfile
