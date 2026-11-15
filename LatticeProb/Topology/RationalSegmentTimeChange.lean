import LatticeProb.Topology.RationalSegmentConnectedInterior
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-! # Segment interiors under increasing time changes -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Countably many almost-sure rational segment conditions imply, on one event,
the corresponding geometry for every real segment and every increasing time
order isomorphism. -/
theorem ae_connected_interior_image_comp_orderIso_of_rational_segments
    {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [TopologicalSpace X] [T2Space X] (η : Ω → ℝ → X)
    (hcont : ∀ᵐ ω ∂μ, Continuous (η ω))
    (hrat : ∀ p q : ℚ, (p : ℝ) < (q : ℝ) →
      ∀ᵐ ω ∂μ, IsConnected (interior (η ω '' Icc (p : ℝ) (q : ℝ))) ∧
        closure (interior (η ω '' Icc (p : ℝ) (q : ℝ))) =
          η ω '' Icc (p : ℝ) (q : ℝ)) :
    ∀ᵐ ω ∂μ, ∀ (φ : ℝ ≃o ℝ) (s t : ℝ), s < t →
      IsConnected (interior ((η ω ∘ φ) '' Icc s t)) ∧
        closure (interior ((η ω ∘ φ) '' Icc s t)) = (η ω ∘ φ) '' Icc s t := by
  have hrat' : ∀ᵐ ω ∂μ, ∀ p q : ℚ, (p : ℝ) < (q : ℝ) →
      IsConnected (interior (η ω '' Icc (p : ℝ) (q : ℝ))) ∧
        closure (interior (η ω '' Icc (p : ℝ) (q : ℝ))) =
          η ω '' Icc (p : ℝ) (q : ℝ) := by
    apply ae_all_iff.mpr
    intro p
    apply ae_all_iff.mpr
    intro q
    by_cases h : (p : ℝ) < (q : ℝ)
    · filter_upwards [hrat p q h] with ω hω _ using hω
    · exact Filter.Eventually.of_forall (fun _ h' => (h h').elim)
  filter_upwards [hcont, hrat'] with ω hc hr φ s t hst
  have h := connected_interior_image_of_rational_subsegments (η ω) hc
    (φ.strictMono hst)
    (fun p q _ hpq _ => (hr p q hpq).1)
    (fun p q _ hpq _ => (hr p q hpq).2)
  simpa only [Set.image_comp, φ.image_Icc] using h

end LatticeProb
