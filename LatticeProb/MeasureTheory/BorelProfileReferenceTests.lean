import LatticeProb.MeasureTheory.MeasurableProfileBorelSeparable
import LatticeProb.MeasureTheory.SeparableReferenceCover
import LatticeProb.MeasureTheory.CountableReferenceMeasurability
import LatticeProb.MeasureTheory.JointProfileReferenceDiscrepancy
import LatticeProb.MeasureTheory.MeasurableDensityProfile

/-!
# Profile reference tests over Borel reference measures

For a finite Borel measure on a second-countable space, measurable profiles with values in a
second-countable label space form a separable pseudometric space. Countable reference families
of valid profiles therefore exist without a supplied countable dense label set or measure-dense
set algebra, and the reference tests for scalar observables and finite kernels hold under the
remaining hypotheses: measurable discrepancy tests (or a jointly measurable lift, or density
profiles of a finite kernel) and uniform control of the observable by the discrepancy.
-/

open Set MeasureTheory TopologicalSpace ProbabilityTheory
open scoped ENNReal

namespace LatticeProb.MeasurableProfile

/-- Over a finite Borel measure on a second-countable space, every nonempty family of valid
measurable profiles admits a countable reference cover when its discrepancy is dominated by
integrated distance. -/
theorem exists_countable_valid_reference_cover_of_borel
    {α E Y : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [SecondCountableTopology α] [PseudoEMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E]
    (μ : Measure α) [IsFiniteMeasure μ] (V : Set (MeasurableProfile (E := E) μ))
    (hV : V.Nonempty) (q : MeasurableProfile (E := E) μ → Y) (δ : Y → Y → ℝ)
    (hδ : ∀ f ∈ V, ∀ g ∈ V, δ (q f) (q g) ≤ (integralDist μ f g).toReal) :
    ∃ r : ℕ → MeasurableProfile (E := E) μ, (∀ n, r n ∈ V) ∧
      ∀ f ∈ V, ∀ ε > 0, ∃ n, δ (q (r n)) (q f) < ε := by
  have : SeparableSpace (MeasurableProfile (E := E) μ) := separableSpace_of_borel μ
  exact LatticeProb.exists_countable_reference_cover V hV q δ hδ

/-- Over a finite Borel measure on a second-countable space, measurable discrepancy tests and
a uniform scalar bound imply measurability of an observable on values represented by valid
measurable profiles. -/
theorem measurable_scalar_of_valid_reference_tests_of_borel
    {α E Y Ω : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [SecondCountableTopology α] [PseudoEMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    (μ : Measure α) [IsFiniteMeasure μ] (V : Set (MeasurableProfile (E := E) μ))
    (hV : V.Nonempty) (q : MeasurableProfile (E := E) μ → Y) (δ : Y → Y → ℝ)
    (hδ : ∀ f ∈ V, ∀ g ∈ V, δ (q f) (q g) ≤ (integralDist μ f g).toReal)
    (z : Ω → Y) (F : Y → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hz : ∀ ω, ∃ g ∈ V, q g = z ω)
    (htest : ∀ f ∈ V, Measurable fun ω => δ (q f) (z ω))
    (hbound : ∀ f ∈ V, ∀ g ∈ V, |F (q g) - F (q f)| ≤ C * δ (q f) (q g)) :
    Measurable (fun ω => F (z ω)) := by
  obtain ⟨r, hr, hcover⟩ := exists_countable_valid_reference_cover_of_borel μ V hV q δ hδ
  apply LatticeProb.measurable_of_countable_reference_discrepancies
    (fun ω => F (z ω)) (fun n => F (q (r n))) (fun n ω => δ (q (r n)) (z ω)) C hC
  · exact fun n => htest (r n) (hr n)
  · intro n ω
    obtain ⟨g, hg, hq⟩ := hz ω
    rw [← hq]
    exact hbound (r n) (hr n) g hg
  · intro ω ε hε
    obtain ⟨g, hg, hq⟩ := hz ω
    obtain ⟨n, hn⟩ := hcover g hg ε hε
    exact ⟨n, hq ▸ hn⟩

/-- Over a finite Borel measure on a second-countable space, measurable discrepancy tests and
uniform evaluation bounds yield a finite kernel on values represented by valid measurable
profiles. -/
theorem exists_finite_kernel_of_valid_reference_tests_of_borel
    {α E Y Ω X : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [SecondCountableTopology α] [PseudoEMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    [MeasurableSpace X]
    (μ : Measure α) [IsFiniteMeasure μ] (V : Set (MeasurableProfile (E := E) μ))
    (hV : V.Nonempty) (q : MeasurableProfile (E := E) μ → Y) (δ : Y → Y → ℝ)
    (hδ : ∀ f ∈ V, ∀ g ∈ V, δ (q f) (q g) ≤ (integralDist μ f g).toReal)
    (z : Ω → Y) (M : Y → Measure X) (K : ℝ≥0∞) (hK : K < ∞)
    (hfinite : ∀ ω, M (z ω) univ ≤ K) (C : ℝ) (hC : 0 ≤ C)
    (hz : ∀ ω, ∃ g ∈ V, q g = z ω)
    (htest : ∀ f ∈ V, Measurable fun ω => δ (q f) (z ω))
    (hbound : ∀ s, MeasurableSet s → ∀ f ∈ V, ∀ g ∈ V,
      |(M (q g) s).toReal - (M (q f) s).toReal| ≤ C * δ (q f) (q g)) :
    ∃ κ : Kernel Ω X, IsFiniteKernel κ ∧ ∀ ω, κ ω = M (z ω) := by
  obtain ⟨r, hr, hcover⟩ := exists_countable_valid_reference_cover_of_borel μ V hV q δ hδ
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

/-- Over a finite Borel measure on a second-countable space, a jointly measurable valid lift
supplies the reference tests for a scalar observable. -/
theorem measurable_scalar_of_joint_valid_lift_of_borel
    {α E Y Ω : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [SecondCountableTopology α] [PseudoEMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    (μ : Measure α) [IsFiniteMeasure μ] (V : Set (MeasurableProfile (E := E) μ))
    (hV : V.Nonempty) (q : MeasurableProfile (E := E) μ → Y) (δ : Y → Y → ℝ)
    (hδ : ∀ f ∈ V, ∀ g ∈ V, δ (q f) (q g) ≤ (integralDist μ f g).toReal)
    (z : Ω → Y) (g : Ω → MeasurableProfile (E := E) μ)
    (hgV : ∀ ω, g ω ∈ V) (hgq : ∀ ω, q (g ω) = z ω)
    (hg : Measurable (fun p : Ω × α => (g p.1).1 p.2))
    (F : Y → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ f ∈ V, ∀ g ∈ V, |F (q g) - F (q f)| ≤ C * δ (q f) (q g)) :
    Measurable (fun ω => F (z ω)) := by
  have hm : Measurable (fun ω => F (q (g ω))) := by
    apply measurable_scalar_of_valid_reference_tests_of_borel μ V hV
      id (fun f g => (integralDist μ f g).toReal) (by intros; rfl)
      g (fun f => F (q f)) C hC
    · exact fun ω => ⟨g ω, hgV ω, rfl⟩
    · intro f _
      exact measurable_integralDist_toReal μ f g hg
    · intro f hf f' hf'
      exact (hbound f hf f' hf').trans (mul_le_mul_of_nonneg_left (hδ f hf f' hf') hC)
  simpa only [hgq] using hm

/-- Over a finite Borel measure on a second-countable space, a jointly measurable valid lift
supplies the reference tests for a finite kernel. -/
theorem exists_finite_kernel_of_joint_valid_lift_of_borel
    {α E Y Ω X : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [SecondCountableTopology α] [PseudoEMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    [MeasurableSpace X]
    (μ : Measure α) [IsFiniteMeasure μ] (V : Set (MeasurableProfile (E := E) μ))
    (hV : V.Nonempty) (q : MeasurableProfile (E := E) μ → Y) (δ : Y → Y → ℝ)
    (hδ : ∀ f ∈ V, ∀ g ∈ V, δ (q f) (q g) ≤ (integralDist μ f g).toReal)
    (z : Ω → Y) (g : Ω → MeasurableProfile (E := E) μ)
    (hgV : ∀ ω, g ω ∈ V) (hgq : ∀ ω, q (g ω) = z ω)
    (hg : Measurable (fun p : Ω × α => (g p.1).1 p.2))
    (M : Y → Measure X) (K : ℝ≥0∞) (hK : K < ∞)
    (hfinite : ∀ ω, M (z ω) univ ≤ K) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ s, MeasurableSet s → ∀ f ∈ V, ∀ g ∈ V,
      |(M (q g) s).toReal - (M (q f) s).toReal| ≤ C * δ (q f) (q g)) :
    ∃ κ : Kernel Ω X, IsFiniteKernel κ ∧ ∀ ω, κ ω = M (z ω) := by
  have hf : ∀ ω, M (q (g ω)) univ ≤ K := by simpa only [hgq] using hfinite
  obtain ⟨κ, hκ, hκeq⟩ := exists_finite_kernel_of_valid_reference_tests_of_borel μ
    V hV id (fun f g => (integralDist μ f g).toReal) (by intros; rfl)
    g (fun f => M (q f)) K hK hf C hC (fun ω => ⟨g ω, hgV ω, rfl⟩)
    (fun f _ => measurable_integralDist_toReal μ f g hg)
    (fun s hs f hf f' hf' =>
      (hbound s hs f hf f' hf').trans (mul_le_mul_of_nonneg_left (hδ f hf f' hf') hC))
  exact ⟨κ, hκ, fun ω => (hκeq ω).trans (congrArg M (hgq ω))⟩

/-- A uniformly controlled scalar observable of nonnegative density profiles of a finite
kernel, with respect to a finite reference measure on the real line, is measurable. Profiles
may be chosen independently up to almost-everywhere equality. -/
theorem measurable_scalar_of_finite_kernel_densities_of_borel
    {Y Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (V : Set (MeasurableProfile (E := ℝ) μ))
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
    apply measurable_scalar_of_valid_reference_tests_of_borel μ V hV
      id (fun f g => (integralDist μ f g).toReal) (by intros; rfl)
      g (fun f => F (q f)) C hC
    · exact fun ω => ⟨g ω, hgV ω, rfl⟩
    · intro f _
      have h := measurable_integralDist_toReal μ f g' hgj
      simpa only [id_eq, hdist] using h
    · intro f hf f' hf'
      exact (hbound f hf f' hf').trans (mul_le_mul_of_nonneg_left (hδ f hf f' hf') hC)
  simpa only [hgq] using hm

/-- Uniformly controlled measure-valued observables of nonnegative density profiles of a
finite kernel, with respect to a finite reference measure on the real line, form a finite
kernel. -/
theorem exists_finite_kernel_of_finite_kernel_densities_of_borel
    {Y Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (V : Set (MeasurableProfile (E := ℝ) μ))
    (hV : V.Nonempty) (q : MeasurableProfile (E := ℝ) μ → Y) (δ : Y → Y → ℝ)
    (hδ : ∀ f ∈ V, ∀ g ∈ V, δ (q f) (q g) ≤ (integralDist μ f g).toReal)
    (z : Ω → Y) (g : Ω → MeasurableProfile (E := ℝ) μ)
    (hgV : ∀ ω, g ω ∈ V) (hgq : ∀ ω, q (g ω) = z ω)
    (κ : Kernel Ω ℝ) [IsFiniteKernel κ]
    (hgpos : ∀ ω, ∀ᵐ t ∂μ, 0 ≤ (g ω).1 t)
    (hgκ : ∀ ω, κ ω = μ.withDensity (fun t => ENNReal.ofReal ((g ω).1 t)))
    (M : Y → Measure X) (K : ℝ≥0∞) (hK : K < ∞)
    (hfinite : ∀ ω, M (z ω) univ ≤ K) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ s, MeasurableSet s → ∀ f ∈ V, ∀ g ∈ V,
      |(M (q g) s).toReal - (M (q f) s).toReal| ≤ C * δ (q f) (q g)) :
    ∃ η : Kernel Ω X, IsFiniteKernel η ∧ ∀ ω, η ω = M (z ω) := by
  obtain ⟨G, hG, hGeq⟩ := exists_measurable_real_density_profile μ κ
  let g' : Ω → MeasurableProfile (E := ℝ) μ := fun ω =>
    ⟨fun t => G (ω, t), (hG.comp (measurable_const.prodMk measurable_id)).aemeasurable⟩
  have hgj : Measurable (fun p : Ω × ℝ => (g' p.1).1 p.2) := hG
  have hdist (f : MeasurableProfile (E := ℝ) μ) (ω : Ω) :
      integralDist μ f (g' ω) = integralDist μ f (g ω) := by
    apply lintegral_congr_ae
    filter_upwards [hGeq ω (g ω).1 (g ω).2 (hgpos ω) (hgκ ω)] with t ht
    simp only [g', ht]
  have hf : ∀ ω, M (q (g ω)) univ ≤ K := by simpa only [hgq] using hfinite
  obtain ⟨η, hη, hηeq⟩ := exists_finite_kernel_of_valid_reference_tests_of_borel μ
    V hV id (fun f g => (integralDist μ f g).toReal) (by intros; rfl)
    g (fun f => M (q f)) K hK hf C hC (fun ω => ⟨g ω, hgV ω, rfl⟩)
    (fun f _ => by
      have h := measurable_integralDist_toReal μ f g' hgj
      simpa only [id_eq, hdist] using h)
    (fun s hs f hf f' hf' =>
      (hbound s hs f hf f' hf').trans (mul_le_mul_of_nonneg_left (hδ f hf f' hf') hC))
  exact ⟨η, hη, fun ω => (hηeq ω).trans (congrArg M (hgq ω))⟩

end LatticeProb.MeasurableProfile
