import LatticeProb.Prob.CorrelatedBMContourFiber
import LatticeProb.Topology.RandomCurveComponentFrontier
import Mathlib.Topology.Connected.LocallyConnected

/-! # Frontiers of curve segments with Brownian contour fibres -/

set_option autoImplicit false

open MeasureTheory Set
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- The components of a measure-parametrized curve segment have null frontiers
when fixed-time curve fibres are contained in Brownian contour classes. -/
theorem ae_measure_frontier_components_of_contour_relation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SigmaFinite P]
    {γ : ℝ} (Z : Ω → Path2) (f : Ω → C(ℝ, ℂ)) (μ : Ω → Measure ℂ)
    (a b : ℝ) (hZ : AEMeasurable Z P)
    (hLaw : IsCorrelatedBM2 γ (P.map Z)) (hf : Measurable f)
    (hrel : ∀ u, ∀ᵐ ω ∂P, ∀ t, f ω t = f ω u → Relation.EqvGen
      (fun s t => DirectRel (fun v => lrCoord 0 v (Z ω)) s t ∨
        DirectRel (fun v => lrCoord 1 v (Z ω)) s t) u t)
    (hproper : ∀ᵐ ω ∂P, IsProperMap (f ω))
    (hsurj : ∀ᵐ ω ∂P, Function.Surjective (f ω))
    (hmap : ∀ᵐ ω ∂P, Measure.map (f ω) volume = μ ω)
    (hmass : ∀ᵐ ω ∂P, μ ω (f ω '' Icc a b) = volume (Icc a b)) :
    ∀ᵐ ω ∂P, ∀ x : ℂ,
      μ ω (frontier (connectedComponentIn (interior (f ω '' Icc a b)) x)) = 0 := by
  obtain ⟨B, hBsub, hBcount, hBbasis⟩ :=
    (TopologicalSpace.IsTopologicalBasis.isOpen_isPreconnected (α := ℂ)).exists_countable
  have : Countable B := hBcount.to_subtype
  apply ae_measure_frontier_curve_components_eq_zero P (fun i : B => i.val) f μ a b hf
  · intro i
    exact (hBsub i.property).1
  · intro V hV z hz
    obtain ⟨U, hU, hzU, hUV⟩ := hBbasis.isOpen_iff.mp hV z hz
    exact ⟨⟨U, hU⟩, hzU, hUV⟩
  · intro u hu
    filter_upwards [ae_mem_interior_image_Icc_of_contour_relation hZ hLaw u
      (hrel u) hproper hsurj] with ω hω
    exact hω a b hu.1 hu.2
  · exact hmap
  · exact hmass

end LatticeProb.CorrelatedBM
