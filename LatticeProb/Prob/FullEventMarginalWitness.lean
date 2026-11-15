import LatticeProb.Prob.AnalyticWitnessTransfer

/-! # Marginal witnesses from a full event -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- A full event of pairs has a measurable full set of first coordinates,
each with a witness in the event. -/
theorem exists_measurable_full_marginal_witnesses_of_ae
    {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure (X × Y)) [IsFiniteMeasure μ] {A : Set (X × Y)}
    (hfull : ∀ᵐ p ∂μ, p ∈ A) :
    ∃ G : Set X, MeasurableSet G ∧ (∀ᵐ x ∂μ.map Prod.fst, x ∈ G) ∧
      ∀ x ∈ G, ∃ y, (x, y) ∈ A := by
  have hA : NullMeasurableSet A μ := by
    simpa only [compl_compl] using
      (NullMeasurableSet.of_null (show μ Aᶜ = 0 from ae_iff.1 hfull)).compl
  exact exists_measurable_full_marginal_witnesses μ hA hfull

/-- A random variable with the same first marginal inherits witnesses from
an almost-sure event of pairs. -/
theorem ae_exists_witness_of_marginal_law_of_ae
    {X Y Ω : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace Ω] (μ : Measure (X × Y)) [IsFiniteMeasure μ]
    (P : Measure Ω) (Z : Ω → X) (hZ : Measurable Z) (hlaw : P.map Z = μ.map Prod.fst)
    {A : Set (X × Y)} (hfull : ∀ᵐ p ∂μ, p ∈ A) :
    ∀ᵐ ω ∂P, ∃ y, (Z ω, y) ∈ A := by
  have hA : NullMeasurableSet A μ := by
    simpa only [compl_compl] using
      (NullMeasurableSet.of_null (show μ Aᶜ = 0 from ae_iff.1 hfull)).compl
  exact ae_exists_witness_of_marginal_law μ P Z hZ hlaw hA hfull

end LatticeProb
