import LatticeProb.Prob.AnalyticUniversalMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! # Transfer of almost-sure witnesses through a marginal law -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- A full-measure null-measurable set of pairs has a measurable, full-measure
set of first coordinates, each admitting a witness in the original set. -/
theorem exists_measurable_full_marginal_witnesses
    {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure (X × Y)) [IsFiniteMeasure μ] {A : Set (X × Y)}
    (hA : NullMeasurableSet A μ) (hfull : ∀ᵐ p ∂μ, p ∈ A) :
    ∃ G : Set X, MeasurableSet G ∧ (∀ᵐ x ∂μ.map Prod.fst, x ∈ G) ∧
      ∀ x ∈ G, ∃ y, (x, y) ∈ A := by
  obtain ⟨B, hBA, hBm, hBeq⟩ := hA.exists_measurable_subset_ae_eq
  have hBfull : ∀ᵐ p ∂μ, p ∈ B := by
    filter_upwards [hfull, hBeq] with p hp heq
    exact heq.mpr hp
  have hproj : AnalyticSet (Prod.fst '' B) := hBm.analyticSet.image_of_continuous continuous_fst
  have : IsFiniteMeasure (μ.map Prod.fst) := Measure.isFiniteMeasure_map μ Prod.fst
  obtain ⟨G, hGsub, hGm, hGeq⟩ :=
    (AnalyticSet.nullMeasurableSet (μ.map Prod.fst) hproj).exists_measurable_subset_ae_eq
  have hGfull : ∀ᵐ p ∂μ, p.1 ∈ G := by
    have heq := ae_of_ae_map measurable_fst.aemeasurable hGeq
    filter_upwards [hBfull, heq] with p hp he
    apply he.mpr
    exact ⟨p, hp, rfl⟩
  refine ⟨G, hGm, (ae_map_iff measurable_fst.aemeasurable hGm).2 hGfull, ?_⟩
  intro x hx
  obtain ⟨⟨x', y⟩, hp, he⟩ := hGsub hx
  cases he
  exact ⟨y, hBA hp⟩

/-- A random variable with the same marginal law inherits almost-sure existence
of witnesses, without requiring a measurable choice of witness. -/
theorem ae_exists_witness_of_marginal_law
    {X Y Ω : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace Ω] (μ : Measure (X × Y)) [IsFiniteMeasure μ]
    (P : Measure Ω) (Z : Ω → X) (hZ : Measurable Z) (hlaw : P.map Z = μ.map Prod.fst)
    {A : Set (X × Y)} (hA : NullMeasurableSet A μ) (hfull : ∀ᵐ p ∂μ, p ∈ A) :
    ∀ᵐ ω ∂P, ∃ y, (Z ω, y) ∈ A := by
  obtain ⟨G, hGm, hGfull, hG⟩ := exists_measurable_full_marginal_witnesses μ hA hfull
  rw [← hlaw] at hGfull
  filter_upwards [(ae_map_iff hZ.aemeasurable hGm).1 hGfull] with ω hω
  exact hG _ hω

end LatticeProb
