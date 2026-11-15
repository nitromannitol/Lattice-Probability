import LatticeProb.Prob.AnalyticUniqueSection
import LatticeProb.Prob.AnalyticWitnessTransfer

/-! # Selection from unique joint witnesses -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- If a full-measure joint witness set determines the same value for every
witness above a given first coordinate, the value has a measurable version. -/
theorem exists_measurable_of_unique_joint_witness
    {X Y Z : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z] [Nonempty Z]
    (μ : Measure (X × Y)) [IsFiniteMeasure μ] {A : Set (X × Y)}
    (hA : NullMeasurableSet A μ) (hfull : ∀ᵐ p ∂μ, p ∈ A)
    {E : Set ((X × Y) × Z)} (hE : MeasurableSet E)
    (hex : ∀ p ∈ A, ∃ z, (p, z) ∈ E)
    (hu : ∀ x y y' z z', (x, y) ∈ A → (x, y') ∈ A →
      ((x, y), z) ∈ E → ((x, y'), z') ∈ E → z = z') :
    ∃ f : X → Z, Measurable f ∧ ∀ᵐ p ∂μ, (p, f p.1) ∈ E := by
  obtain ⟨B, hBA, hBm, hBeq⟩ := hA.exists_measurable_subset_ae_eq
  have hBfull : ∀ᵐ p ∂μ, p ∈ B := by
    filter_upwards [hfull, hBeq] with p hp he
    exact he.mpr hp
  let H : Set ((X × Y) × Z) := E ∩ Prod.fst ⁻¹' B
  let G : Set (X × Z) := (fun p : (X × Y) × Z => (p.1.1, p.2)) '' H
  have hG : AnalyticSet G := by
    apply (hE.inter (hBm.preimage measurable_fst)).analyticSet.image_of_continuous
    exact (continuous_fst.comp continuous_fst).prodMk continuous_snd
  obtain ⟨S, hSm, hSfull, hS⟩ :=
    exists_measurable_full_marginal_witnesses μ hBm.nullMeasurableSet hBfull
  have huniq : ∀ᵐ x ∂μ.map Prod.fst, ∃! z, (x, z) ∈ G := by
    filter_upwards [hSfull] with x hx
    obtain ⟨y, hy⟩ := hS x hx
    obtain ⟨z, hz⟩ := hex (x, y) (hBA hy)
    refine ⟨z, ⟨((x, y), z), ⟨hz, hy⟩, rfl⟩, ?_⟩
    rintro z' ⟨⟨⟨x', y'⟩, w⟩, ⟨hw, hy'⟩, he⟩
    cases he
    exact hu _ y' y _ z (hBA hy') (hBA hy) hw hz
  have : IsFiniteMeasure (μ.map Prod.fst) := Measure.isFiniteMeasure_map μ Prod.fst
  obtain ⟨f, hfm, hf⟩ := exists_measurable_of_ae_unique_analytic_section (μ.map Prod.fst) hG huniq
  refine ⟨f, hfm, ?_⟩
  have hf' := ae_of_ae_map measurable_fst.aemeasurable hf
  filter_upwards [hBfull, hf'] with ⟨x, y⟩ hy hfxy
  obtain ⟨z, hz⟩ := hex (x, y) (hBA hy)
  obtain ⟨⟨⟨x', y'⟩, w⟩, ⟨hw, hy'⟩, he⟩ := hfxy
  cases he
  have h : f x = z := hu x y' y (f x) z (hBA hy') (hBA hy) hw hz
  rw [h]
  exact hz

end LatticeProb
