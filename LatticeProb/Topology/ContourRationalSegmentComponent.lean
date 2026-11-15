import LatticeProb.Topology.RationalSegmentTimeChange
import LatticeProb.Prob.CorrelatedBMContourFiber

/-! # Components of time-changed curve segments -/

set_option autoImplicit false

open Set MeasureTheory
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- For a fixed contour time, connected regular-closed rational segment geometry
passes through a random increasing time change and identifies the component of
any segment containing that time. -/
theorem ae_component_closure_eq_segment_of_rational_geometry
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (η f : Ω → ℝ → ℂ) {γ : ℝ} {Z : Ω → Path2} (a : ℝ)
    (hcont : ∀ᵐ ω ∂P, Continuous (η ω))
    (hrat : ∀ p q : ℚ, (p : ℝ) < (q : ℝ) →
      ∀ᵐ ω ∂P, IsConnected (interior (η ω '' Icc (p : ℝ) (q : ℝ))) ∧
        closure (interior (η ω '' Icc (p : ℝ) (q : ℝ))) =
          η ω '' Icc (p : ℝ) (q : ℝ))
    (htime : ∀ᵐ ω ∂P, ∃ φ : ℝ ≃o ℝ, f ω = η ω ∘ φ)
    (hZ : AEMeasurable Z P) (hLaw : IsCorrelatedBM2 γ (P.map Z))
    (hrel : ∀ᵐ ω ∂P, ∀ t, f ω t = f ω a → Relation.EqvGen
      (fun s t => DirectRel (fun u => lrCoord 0 u (Z ω)) s t ∨
        DirectRel (fun u => lrCoord 1 u (Z ω)) s t) a t)
    (hproper : ∀ᵐ ω ∂P, IsProperMap (f ω))
    (hsurj : ∀ᵐ ω ∂P, Function.Surjective (f ω)) :
    ∀ᵐ ω ∂P, ∀ l r : ℝ, l < a → a < r →
      f ω a ∈ interior (f ω '' Icc l r) ∧
      closure (connectedComponentIn (interior (f ω '' Icc l r)) (f ω a)) =
        f ω '' Icc l r := by
  filter_upwards [ae_connected_interior_image_comp_orderIso_of_rational_segments P η hcont hrat,
    ae_mem_interior_image_Icc_of_contour_relation hZ hLaw a hrel hproper hsurj,
    htime] with ω hgeometry hinter ⟨φ, hφ⟩
  intro l r hl hr
  have hg := hgeometry φ l r (lt_trans hl hr)
  rw [← hφ] at hg
  have ha := hinter l r hl hr
  refine ⟨ha, ?_⟩
  rw [hg.1.isPreconnected.connectedComponentIn ha]
  exact hg.2

end LatticeProb.CorrelatedBM
