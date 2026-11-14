import LatticeProb.Topology.OpenAEIntervalVisits
import LatticeProb.Topology.MeasurableVisitEndpoints
import Mathlib.Topology.Perfect
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Endpoints of a component traced by a curve -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- An interval whose image is the closure of a nonempty open set in a perfect space
has positive length. -/
theorem interval_lt_of_image_eq_closure_open
    {E : Type*} [TopologicalSpace E] [PerfectSpace E]
    (η : ℝ → E) (U : Set E) (a b : ℝ)
    (hU : IsOpen U) (hne : U.Nonempty) (himage : η '' Icc a b = closure U) :
    a < b := by
  by_contra h
  have hba : b ≤ a := le_of_not_gt h
  rcases eq_or_lt_of_le hba with heq | hlt
  · subst b
    have hsub : U ⊆ interior (η '' Icc a a) :=
      interior_maximal (himage ▸ subset_closure) hU
    rw [Icc_self, image_singleton, interior_singleton] at hsub
    exact hne.ne_empty (subset_empty_iff.mp hsub)
  · have hsub : U ⊆ η '' Icc a b := himage ▸ subset_closure
    rw [Icc_eq_empty (not_le_of_gt hlt), image_empty] at hsub
    exact hne.ne_empty (subset_empty_iff.mp hsub)

/-- Measurable rational visits identify both endpoints when the open visit set agrees
almost everywhere with the time interval. -/
theorem measurable_endpoints_of_open_curve_visits
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [PerfectSpace E]
    (η : Ω → ℝ → E) (U : Ω → Set E) (a b : Ω → ℝ)
    (hη : ∀ ω, Continuous (η ω)) (hU : ∀ ω, IsOpen (U ω))
    (hne : ∀ ω, (U ω).Nonempty)
    (himage : ∀ ω, η ω '' Icc (a ω) (b ω) = closure (U ω))
    (hvisit : ∀ q : ℚ, MeasurableSet {ω | η ω q ∈ U ω})
    (hae : ∀ ω, ∀ᵐ t ∂volume, η ω t ∈ U ω ↔ t ∈ Ioo (a ω) (b ω)) :
    Measurable a ∧ Measurable b := by
  apply measurable_endpoints_of_rational_visits (fun ω q => η ω q ∈ U ω) a b hvisit
  · intro ω q hq
    exact (rational_visits_of_open_ae_interval volume (η ω ⁻¹' U ω) (a ω) (b ω)
      ((hU ω).preimage (hη ω))
      (interval_lt_of_image_eq_closure_open (η ω) (U ω) (a ω) (b ω)
        (hU ω) (hne ω) (himage ω)) (hae ω)).1 q hq
  · intro ω t ht
    exact (rational_visits_of_open_ae_interval volume (η ω ⁻¹' U ω) (a ω) (b ω)
      ((hU ω).preimage (hη ω))
      (interval_lt_of_image_eq_closure_open (η ω) (U ω) (a ω) (b ω)
        (hU ω) (hne ω) (himage ω)) (hae ω)).2.1 t ht
  · intro ω t ht
    exact (rational_visits_of_open_ae_interval volume (η ω ⁻¹' U ω) (a ω) (b ω)
      ((hU ω).preimage (hη ω))
      (interval_lt_of_image_eq_closure_open (η ω) (U ω) (a ω) (b ω)
        (hU ω) (hne ω) (himage ω)) (hae ω)).2.2 t ht

end LatticeProb
